#include <algorithm>
#include <array>
#include <cassert>
#include <climits>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <exception>
#include <features.h>
#include <functional>
#include <initializer_list>
#include <iosfwd>
#include <iterator>
#include <limits>
#include <memory>
#include <stdc-predef.h>
#include <stdexcept>
#include <string>
#include <string_view>
#include <tuple>
#include <type_traits>
#include <utility>
namespace folly
{
template <typename T>
constexpr T constexpr_max(T a)
{
  return a;
}
template <typename T, typename... Ts>
constexpr T constexpr_max(T a, T b, Ts... ts)
{
  return b < a ? constexpr_max(a, ts...) : constexpr_max(b, ts...);
}
template <typename T>
constexpr T constexpr_min(T a)
{
  return a;
}
template <typename T, typename... Ts>
constexpr T constexpr_min(T a, T b, Ts... ts)
{
  return b < a ? constexpr_min(b, ts...) : constexpr_min(a, ts...);
}
template <typename T, typename Less>
constexpr T const &constexpr_clamp(
    T const &v, T const &lo, T const &hi, Less less)
{
  return less(v, lo) ? lo : less(hi, v) ? hi
                                        : v;
}
template <typename T>
constexpr T const &constexpr_clamp(T const &v, T const &lo, T const &hi)
{
  return constexpr_clamp(v, lo, hi, std::less<T>{});
}
namespace detail
{
template <typename T, typename = void>
struct constexpr_abs_helper
{
};
template <typename T>
struct constexpr_abs_helper<
    T,
    typename std::enable_if<std::is_floating_point<T>::value>::type>
{
  static constexpr T go(T t)
  {
    return t < static_cast<T>(0) ? -t : t;
  }
};
template <typename T>
struct constexpr_abs_helper<
    T,
    typename std::enable_if<
        std::is_integral<T>::value && !std::is_same<T, bool>::value &&
        std::is_unsigned<T>::value>::type>
{
  static constexpr T go(T t)
  {
    return t;
  }
};
template <typename T>
struct constexpr_abs_helper<
    T,
    typename std::enable_if<
        std::is_integral<T>::value && !std::is_same<T, bool>::value &&
        std::is_signed<T>::value>::type>
{
  static constexpr typename std::make_unsigned<T>::type go(T t)
  {
    return typename std::make_unsigned<T>::type(t < static_cast<T>(0) ? -t : t);
  }
};
} // namespace detail
template <typename T>
constexpr auto constexpr_abs(T t)
    -> decltype(detail::constexpr_abs_helper<T>::go(t))
{
  return detail::constexpr_abs_helper<T>::go(t);
}
namespace detail
{
template <typename T>
constexpr T constexpr_log2_(T a, T e)
{
  return e == T(1) ? a : constexpr_log2_(a + T(1), e / T(2));
}
template <typename T>
constexpr T constexpr_log2_ceil_(T l2, T t)
{
  return l2 + T(T(1) << l2 < t ? 1 : 0);
}
template <typename T>
constexpr T constexpr_square_(T t)
{
  return t * t;
}
} // namespace detail
template <typename T>
constexpr T constexpr_log2(T t)
{
  return detail::constexpr_log2_(T(0), t);
}
template <typename T>
constexpr T constexpr_log2_ceil(T t)
{
  return detail::constexpr_log2_ceil_(constexpr_log2(t), t);
}
template <typename T>
constexpr T constexpr_ceil(T t, T round)
{
  return round == T(0)
             ? t
             : ((t + (t < T(0) ? T(0) : round - T(1))) / round) * round;
}
template <typename T>
constexpr T constexpr_pow(T base, std::size_t exp)
{
  return exp == 0 ? T(1)
         : exp == 1 ? base
                    : detail::constexpr_square_(constexpr_pow(base, exp / 2)) *
                          (exp % 2 ? base : T(1));
}
template <typename T>
constexpr std::size_t constexpr_find_last_set(T const t)
{
  using U = std::make_unsigned_t<T>;
  return t == T(0) ? 0 : 1 + constexpr_log2(static_cast<U>(t));
}
namespace detail
{
template <typename U>
constexpr std::size_t constexpr_find_first_set_(
    std::size_t s, std::size_t a, U const u)
{
  return s == 0 ? a
                : constexpr_find_first_set_(
                    s / 2, a + s * bool((u >> a) % (U(1) << s) == U(0)), u);
}
} // namespace detail
template <typename T>
constexpr std::size_t constexpr_find_first_set(T t)
{
  using U = std::make_unsigned_t<T>;
  using size = std::integral_constant<std::size_t, sizeof(T) * 4>;
  return t == T(0)
             ? 0
             : 1 + detail::constexpr_find_first_set_(size{}, 0, static_cast<U>(t));
}
template <typename T>
constexpr T constexpr_add_overflow_clamped(T a, T b)
{
  using L = std::numeric_limits<T>;
  using M = std::intmax_t;
  static_assert(
      !std::is_integral<T>::value || sizeof(T) <= sizeof(M),
      "Integral type too large!");
  return
      !std::is_integral<T>::value ? a + b :
      sizeof(T) < sizeof(M)
          ? T(constexpr_clamp(
              static_cast<M>(a) + static_cast<M>(b),
              static_cast<M>(L::min()),
              static_cast<M>(L::max())))
          :
          !(a < 0) ? a + constexpr_min(b, T(L::max() - a)) :
          !(b < 0) ? a + b
                   :
                   a + constexpr_max(b, T(L::min() - a));
}
template <typename T>
constexpr T constexpr_sub_overflow_clamped(T a, T b)
{
  using L = std::numeric_limits<T>;
  using M = std::intmax_t;
  static_assert(
      !std::is_integral<T>::value || sizeof(T) <= sizeof(M),
      "Integral type too large!");
  return
      !std::is_integral<T>::value ? a - b :
      std::is_unsigned<T>::value ? (a < b ? 0 : a - b)
      :
      sizeof(T) < sizeof(M)
          ? T(constexpr_clamp(
              static_cast<M>(a) - static_cast<M>(b),
              static_cast<M>(L::min()),
              static_cast<M>(L::max())))
          :
          (a < 0) == (b < 0) ? a - b :
          L::min() < b ? constexpr_add_overflow_clamped(a, T(-b))
          :
          a < 0 ? a - b
                :
                L::max();
}
template <typename Dst, typename Src>
constexpr typename std::enable_if<std::is_integral<Src>::value, Dst>::type
constexpr_clamp_cast(Src src)
{
  static_assert(
      std::is_integral<Dst>::value && sizeof(Dst) <= sizeof(int64_t),
      "constexpr_clamp_cast can only cast into integral type (up to 64bit)");
  using L = std::numeric_limits<Dst>;
  return
      std::is_signed<Src>::value == std::is_signed<Dst>::value
          ? (
              sizeof(Src) <= sizeof(Dst) ? Dst(src) :
                                         Dst(constexpr_clamp(src, Src(L::min()), Src(L::max()))))
          : std::is_signed<Src>::value && std::is_unsigned<Dst>::value
                ? (
                    src < 0 ? Dst(0) :
                    sizeof(Src) <= sizeof(Dst) ? Dst(src)
                                               :
                                               Dst(constexpr_min(src, Src(L::max()))))
                : (
                    sizeof(Src) < sizeof(Dst) ? Dst(src) :
                                              Dst(constexpr_min(src, Src(L::max()))));
}
namespace detail
{
constexpr double kClampCastLowerBoundDoubleToInt64F = -9223372036854774784.0;
constexpr double kClampCastUpperBoundDoubleToInt64F = 9223372036854774784.0;
constexpr double kClampCastUpperBoundDoubleToUInt64F = 18446744073709549568.0;
constexpr float kClampCastLowerBoundFloatToInt32F = -2147483520.0f;
constexpr float kClampCastUpperBoundFloatToInt32F = 2147483520.0f;
constexpr float kClampCastUpperBoundFloatToUInt32F = 4294967040.0f;
template <typename D, typename S>
constexpr D constexpr_clamp_cast_helper(S src, S sl, S su, D dl, D du)
{
  return src < sl ? dl : (src > su ? du : D(src));
}
} // namespace detail
template <typename Dst, typename Src>
constexpr typename std::enable_if<std::is_floating_point<Src>::value, Dst>::type
constexpr_clamp_cast(Src src)
{
  static_assert(
      std::is_integral<Dst>::value && sizeof(Dst) <= sizeof(int64_t),
      "constexpr_clamp_cast can only cast into integral type (up to 64bit)");
  using L = std::numeric_limits<Dst>;
  return
      (src != src) ? Dst(0) :
      sizeof(Src) > sizeof(Dst) ?
                                detail::constexpr_clamp_cast_helper(
                                    src, Src(L::min()), Src(L::max()), L::min(), L::max())
                                :
                                sizeof(Src) < sizeof(Dst) ? (
                                    src >= 0.0
                                        ? constexpr_clamp_cast<Dst>(
                                            constexpr_clamp_cast<std::uint64_t>(double(src)))
                                        : constexpr_clamp_cast<Dst>(
                                            constexpr_clamp_cast<std::int64_t>(double(src))))
                                :
                                std::is_same<Src, double>::value && std::is_same<Dst, int64_t>::value ?
                                                                                                      detail::constexpr_clamp_cast_helper(
                                                                                                          double(src),
                                                                                                          detail::kClampCastLowerBoundDoubleToInt64F,
                                                                                                          detail::kClampCastUpperBoundDoubleToInt64F,
                                                                                                          L::min(),
                                                                                                          L::max())
                                                                                                      :
                                                                                                      std::is_same<Src, double>::value && std::is_same<Dst, uint64_t>::value ?
                                                                                                                                                                             detail::constexpr_clamp_cast_helper(
                                                                                                                                                                                 double(src),
                                                                                                                                                                                 0.0,
                                                                                                                                                                                 detail::kClampCastUpperBoundDoubleToUInt64F,
                                                                                                                                                                                 L::min(),
                                                                                                                                                                                 L::max())
                                                                                                                                                                             :
                                                                                                                                                                             std::is_same<Src, float>::value && std::is_same<Dst, int32_t>::value ?
                                                                                                                                                                                                                                                  detail::constexpr_clamp_cast_helper(
                                                                                                                                                                                                                                                      float(src),
                                                                                                                                                                                                                                                      detail::kClampCastLowerBoundFloatToInt32F,
                                                                                                                                                                                                                                                      detail::kClampCastUpperBoundFloatToInt32F,
                                                                                                                                                                                                                                                      L::min(),
                                                                                                                                                                                                                                                      L::max())
                                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                                  detail::constexpr_clamp_cast_helper(
                                                                                                                                                                                                                                                      float(src),
                                                                                                                                                                                                                                                      0.0f,
                                                                                                                                                                                                                                                      detail::kClampCastUpperBoundFloatToUInt32F,
                                                                                                                                                                                                                                                      L::min(),
                                                                                                                                                                                                                                                      L::max());
}
} // namespace folly
static_assert(201703L >= 201402L, "__cplusplus >= 201402L");
static_assert(10 >= 5, "__GNUC__ >= 5");
namespace folly
{
constexpr bool kHasUnalignedAccess = true;
}
namespace folly
{
constexpr bool kIsArchArm = 0 == 1;
constexpr bool kIsArchAmd64 = 1 == 1;
constexpr bool kIsArchAArch64 = 0 == 1;
constexpr bool kIsArchPPC64 = 0 == 1;
constexpr bool kIsArchS390X = 0 == 1;
} // namespace folly
namespace folly
{
constexpr bool kIsLibrarySanitizeAddress = false;
constexpr bool kIsSanitizeAddress = false;
constexpr bool kIsSanitizeThread = false;
constexpr bool kIsSanitize = false;
} // namespace folly
namespace folly
{
constexpr auto kIsDebug = true;
}
namespace folly
{
constexpr auto kHasExceptions = true;
}
namespace folly
{
constexpr auto kIsLittleEndian = 1234 == 1234;
constexpr auto kIsBigEndian = !kIsLittleEndian;
} // namespace folly
namespace folly
{
constexpr auto kHasWeakSymbols = true;
}
namespace folly
{
constexpr bool const kHasRtti = 1;
}
namespace folly
{
constexpr auto kIsObjC = false;
constexpr auto kIsMobile = false;
constexpr auto kIsLinux = true;
constexpr auto kIsWindows = false;
constexpr auto kIsApple = false;
constexpr bool kIsAppleIOS = 0 == 1;
constexpr bool kIsAppleMacOS = 0 == 1;
constexpr bool kIsAppleTVOS = 0 == 1;
constexpr bool kIsAppleWatchOS = 0 == 1;
constexpr auto kIsGlibcxx = true;
constexpr auto kGlibcxxVer =
    10
    ;
constexpr auto kIsLibcpp = false;
constexpr auto kIsLibstdcpp = true;
constexpr auto kMscVer = 0;
constexpr auto kGnuc = 10;
constexpr auto kIsClang = false;
constexpr auto kClangVerMajor = 0;
constexpr auto kMicrosoftAbiVer = 0;
constexpr auto kCpplibVer = 0;
} // namespace folly
namespace folly
{
namespace hash
{
class SpookyHashV2
{
public:
  static void Hash128(
      const void *message,
      size_t length,
      uint64_t *hash1,
      uint64_t *hash2);
  static uint64_t Hash64(
      const void *message,
      size_t length,
      uint64_t seed)
  {
    uint64_t hash1 = seed;
    Hash128(message, length, &hash1, &seed);
    return hash1;
  }
  static uint32_t Hash32(
      const void *message,
      size_t length,
      uint32_t seed)
  {
    uint64_t hash1 = seed, hash2 = seed;
    Hash128(message, length, &hash1, &hash2);
    return (uint32_t)hash1;
  }
  void Init(
      uint64_t seed1,
      uint64_t seed2);
  void Update(
      const void *message,
      size_t length);
  void Final(
      uint64_t *hash1,
      uint64_t *hash2) const;
  static inline uint64_t Rot64(uint64_t x, int k)
  {
    return (x << k) | (x >> (64 - k));
  }
  static inline void Mix(
      const uint64_t *data,
      uint64_t &s0, uint64_t &s1, uint64_t &s2, uint64_t &s3,
      uint64_t &s4, uint64_t &s5, uint64_t &s6, uint64_t &s7,
      uint64_t &s8, uint64_t &s9, uint64_t &s10, uint64_t &s11)
  {
    s0 += data[0];
    s2 ^= s10;
    s11 ^= s0;
    s0 = Rot64(s0, 11);
    s11 += s1;
    s1 += data[1];
    s3 ^= s11;
    s0 ^= s1;
    s1 = Rot64(s1, 32);
    s0 += s2;
    s2 += data[2];
    s4 ^= s0;
    s1 ^= s2;
    s2 = Rot64(s2, 43);
    s1 += s3;
    s3 += data[3];
    s5 ^= s1;
    s2 ^= s3;
    s3 = Rot64(s3, 31);
    s2 += s4;
    s4 += data[4];
    s6 ^= s2;
    s3 ^= s4;
    s4 = Rot64(s4, 17);
    s3 += s5;
    s5 += data[5];
    s7 ^= s3;
    s4 ^= s5;
    s5 = Rot64(s5, 28);
    s4 += s6;
    s6 += data[6];
    s8 ^= s4;
    s5 ^= s6;
    s6 = Rot64(s6, 39);
    s5 += s7;
    s7 += data[7];
    s9 ^= s5;
    s6 ^= s7;
    s7 = Rot64(s7, 57);
    s6 += s8;
    s8 += data[8];
    s10 ^= s6;
    s7 ^= s8;
    s8 = Rot64(s8, 55);
    s7 += s9;
    s9 += data[9];
    s11 ^= s7;
    s8 ^= s9;
    s9 = Rot64(s9, 54);
    s8 += s10;
    s10 += data[10];
    s0 ^= s8;
    s9 ^= s10;
    s10 = Rot64(s10, 22);
    s9 += s11;
    s11 += data[11];
    s1 ^= s9;
    s10 ^= s11;
    s11 = Rot64(s11, 46);
    s10 += s0;
  }
  static inline void EndPartial(
      uint64_t &h0, uint64_t &h1, uint64_t &h2, uint64_t &h3,
      uint64_t &h4, uint64_t &h5, uint64_t &h6, uint64_t &h7,
      uint64_t &h8, uint64_t &h9, uint64_t &h10, uint64_t &h11)
  {
    h11 += h1;
    h2 ^= h11;
    h1 = Rot64(h1, 44);
    h0 += h2;
    h3 ^= h0;
    h2 = Rot64(h2, 15);
    h1 += h3;
    h4 ^= h1;
    h3 = Rot64(h3, 34);
    h2 += h4;
    h5 ^= h2;
    h4 = Rot64(h4, 21);
    h3 += h5;
    h6 ^= h3;
    h5 = Rot64(h5, 38);
    h4 += h6;
    h7 ^= h4;
    h6 = Rot64(h6, 33);
    h5 += h7;
    h8 ^= h5;
    h7 = Rot64(h7, 10);
    h6 += h8;
    h9 ^= h6;
    h8 = Rot64(h8, 13);
    h7 += h9;
    h10 ^= h7;
    h9 = Rot64(h9, 38);
    h8 += h10;
    h11 ^= h8;
    h10 = Rot64(h10, 53);
    h9 += h11;
    h0 ^= h9;
    h11 = Rot64(h11, 42);
    h10 += h0;
    h1 ^= h10;
    h0 = Rot64(h0, 54);
  }
  static inline void End(
      const uint64_t *data,
      uint64_t &h0, uint64_t &h1, uint64_t &h2, uint64_t &h3,
      uint64_t &h4, uint64_t &h5, uint64_t &h6, uint64_t &h7,
      uint64_t &h8, uint64_t &h9, uint64_t &h10, uint64_t &h11)
  {
    h0 += data[0];
    h1 += data[1];
    h2 += data[2];
    h3 += data[3];
    h4 += data[4];
    h5 += data[5];
    h6 += data[6];
    h7 += data[7];
    h8 += data[8];
    h9 += data[9];
    h10 += data[10];
    h11 += data[11];
    EndPartial(h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11);
    EndPartial(h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11);
    EndPartial(h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11);
  }
  static inline void ShortMix(uint64_t &h0, uint64_t &h1,
                              uint64_t &h2, uint64_t &h3)
  {
    h2 = Rot64(h2, 50);
    h2 += h3;
    h0 ^= h2;
    h3 = Rot64(h3, 52);
    h3 += h0;
    h1 ^= h3;
    h0 = Rot64(h0, 30);
    h0 += h1;
    h2 ^= h0;
    h1 = Rot64(h1, 41);
    h1 += h2;
    h3 ^= h1;
    h2 = Rot64(h2, 54);
    h2 += h3;
    h0 ^= h2;
    h3 = Rot64(h3, 48);
    h3 += h0;
    h1 ^= h3;
    h0 = Rot64(h0, 38);
    h0 += h1;
    h2 ^= h0;
    h1 = Rot64(h1, 37);
    h1 += h2;
    h3 ^= h1;
    h2 = Rot64(h2, 62);
    h2 += h3;
    h0 ^= h2;
    h3 = Rot64(h3, 34);
    h3 += h0;
    h1 ^= h3;
    h0 = Rot64(h0, 5);
    h0 += h1;
    h2 ^= h0;
    h1 = Rot64(h1, 36);
    h1 += h2;
    h3 ^= h1;
  }
  static inline void ShortEnd(uint64_t &h0, uint64_t &h1,
                              uint64_t &h2, uint64_t &h3)
  {
    h3 ^= h2;
    h2 = Rot64(h2, 15);
    h3 += h2;
    h0 ^= h3;
    h3 = Rot64(h3, 52);
    h0 += h3;
    h1 ^= h0;
    h0 = Rot64(h0, 26);
    h1 += h0;
    h2 ^= h1;
    h1 = Rot64(h1, 51);
    h2 += h1;
    h3 ^= h2;
    h2 = Rot64(h2, 28);
    h3 += h2;
    h0 ^= h3;
    h3 = Rot64(h3, 9);
    h0 += h3;
    h1 ^= h0;
    h0 = Rot64(h0, 47);
    h1 += h0;
    h2 ^= h1;
    h1 = Rot64(h1, 54);
    h2 += h1;
    h3 ^= h2;
    h2 = Rot64(h2, 32);
    h3 += h2;
    h0 ^= h3;
    h3 = Rot64(h3, 25);
    h0 += h3;
    h1 ^= h0;
    h0 = Rot64(h0, 63);
    h1 += h0;
  }
private:
  static void Short(
      const void *message,
      size_t length,
      uint64_t *hash1,
      uint64_t *hash2);
  static constexpr size_t sc_numVars = 12;
  static constexpr size_t sc_blockSize = sc_numVars * 8;
  static constexpr size_t sc_bufSize = 2 * sc_blockSize;
  static constexpr uint64_t sc_const = 0xdeadbeefdeadbeefULL;
  uint64_t m_data[2 * sc_numVars];
  uint64_t m_state[sc_numVars];
  size_t m_length;
  uint8_t m_remainder;
};
} // namespace hash
} // namespace folly
namespace folly
{
namespace detail
{
void *memrchr_fallback(void *s, int c, std::size_t len) noexcept;
void const *memrchr_fallback(void const *s, int c, std::size_t len) noexcept;
} // namespace detail
void *memrchr(void *s, int c, std::size_t len) noexcept;
void const *memrchr(void const *s, int c, std::size_t len) noexcept;
std::size_t strlcpy(char *dest, char const *src, std::size_t size);
} // namespace folly
namespace folly
{
template <typename...>
struct tag_t
{
};
template <typename... T>
inline constexpr tag_t<T...> tag{};
using std::bool_constant;
template <std::size_t I>
using index_constant = std::integral_constant<std::size_t, I>;
namespace detail
{
template <template <typename...> class, typename>
inline constexpr bool is_instantiation_of_v = false;
template <template <typename...> class C, typename... T>
inline constexpr bool is_instantiation_of_v<C, C<T...>> = true;
template <template <typename...> class C, typename... T>
struct is_instantiation_of : bool_constant<is_instantiation_of_v<C, T...>>
{
};
template <typename, typename>
inline constexpr bool is_similar_instantiation_v = false;
template <template <typename...> class C, typename... A, typename... B>
inline constexpr bool
    is_similar_instantiation_v<C<A...>, C<B...>> = true;
template <typename A, typename B>
struct is_similar_instantiation
    : bool_constant<is_similar_instantiation_v<A, B>>
{
};
} // namespace detail
namespace detail
{
struct is_constexpr_default_constructible_
{
  template <typename T>
  static constexpr auto make(tag_t<T>) -> decltype(void(T()), 0)
  {
    return (void(T()), 0);
  }
  template <typename T, int = make(tag<T>)>
  static std::true_type sfinae(T *);
  static std::false_type sfinae(void *);
  template <typename T>
  static constexpr bool apply =
      decltype(sfinae(static_cast<T *>(nullptr)))::value;
};
} // namespace detail
template <typename T>
inline constexpr bool is_constexpr_default_constructible_v =
    detail::is_constexpr_default_constructible_::apply<T>;
template <typename T>
struct is_constexpr_default_constructible
    : bool_constant<is_constexpr_default_constructible_v<T>>
{
};
template <typename T>
using _t = typename T::type;
template <typename T>
struct remove_cvref
{
  using type =
      typename std::remove_cv<typename std::remove_reference<T>::type>::type;
};
template <typename T>
using remove_cvref_t = typename remove_cvref<T>::type;
namespace detail
{
template <typename Src>
struct like_
{
  template <typename Dst>
  using apply = Dst;
};
template <typename Src>
struct like_<Src const>
{
  template <typename Dst>
  using apply = Dst const;
};
template <typename Src>
struct like_<Src volatile>
{
  template <typename Dst>
  using apply = Dst volatile;
};
template <typename Src>
struct like_<Src const volatile>
{
  template <typename Dst>
  using apply = Dst const volatile;
};
template <typename Src>
struct like_<Src &>
{
  template <typename Dst>
  using apply = typename like_<Src>::template apply<Dst> &;
};
template <typename Src>
struct like_<Src &&>
{
  template <typename Dst>
  using apply = typename like_<Src>::template apply<Dst> &&;
};
} // namespace detail
template <typename Src, typename Dst>
using like_t = typename detail::like_<Src>::template apply<remove_cvref_t<Dst>>;
template <typename Src, typename Dst>
struct like
{
  using type = like_t<Src, Dst>;
};
namespace traits_detail
{
template <class T, class...>
struct type_t_
{
  using type = T;
};
} // namespace traits_detail
template <class T, class... Ts>
using type_t = typename traits_detail::type_t_<T, Ts...>::type;
template <class... Ts>
using void_t = type_t<void, Ts...>;
struct nonesuch
{
  ~nonesuch() = delete;
  nonesuch(nonesuch const &) = delete;
  void operator=(nonesuch const &) = delete;
};
namespace detail
{
template <typename Void, typename D, template <typename...> class, typename...>
struct detected_
{
  using value_t = std::false_type;
  using type = D;
};
template <typename D, template <typename...> class T, typename... A>
struct detected_<void_t<T<A...>>, D, T, A...>
{
  using value_t = std::true_type;
  using type = T<A...>;
};
} // namespace detail
template <typename D, template <typename...> class T, typename... A>
using detected_or = detail::detected_<void, D, T, A...>;
template <typename D, template <typename...> class T, typename... A>
using detected_or_t = typename detected_or<D, T, A...>::type;
template <template <typename...> class T, typename... A>
using detected_t = detected_or_t<nonesuch, T, A...>;
template <template <typename...> class T, typename... A>
inline constexpr bool is_detected_v =
    detected_or<nonesuch, T, A...>::value_t::value;
template <template <typename...> class T, typename... A>
struct is_detected : detected_or<nonesuch, T, A...>::value_t
{
};
template <typename T>
using aligned_storage_for_t =
    typename std::aligned_storage<sizeof(T), alignof(T)>::type;
template <class T>
using is_trivially_copyable = std::is_trivially_copyable<T>;
template <class T>
inline constexpr bool is_trivially_copyable_v =
    is_trivially_copyable<T>::value;
namespace traits_detail
{
template <typename T>
using detect_IsRelocatable = typename T::IsRelocatable;
template <class T>
struct IsRelocatable_is_true : std::is_same<typename T::IsRelocatable, std::true_type>
{
};
template <class T>
struct has_true_IsRelocatable : std::conditional<is_detected_v<detect_IsRelocatable, T>, IsRelocatable_is_true<T>, std::false_type>::type
{
};
template <typename T>
using detect_IsZeroInitializable = typename T::IsZeroInitializable;
template <class T>
struct IsZeroInitializable_is_true : std::is_same<typename T::IsZeroInitializable, std::true_type>
{
};
template <class T>
struct has_true_IsZeroInitializable : std::conditional<is_detected_v<detect_IsZeroInitializable, T>, IsZeroInitializable_is_true<T>, std::false_type>::type
{
};
} // namespace traits_detail
struct Ignore
{
  Ignore() = default;
  template <class T>
  constexpr Ignore(const T &)
  {
  }
  template <class T>
  const Ignore &operator=(T const &) const
  {
    return *this;
  }
};
template <class...>
using Ignored = Ignore;
namespace traits_detail_IsEqualityComparable
{
Ignore operator==(Ignore, Ignore);
template <class T, class U = T>
struct IsEqualityComparable
    : std::is_convertible<
          decltype(std::declval<T>() == std::declval<U>()),
          bool>
{
};
} // namespace traits_detail_IsEqualityComparable
using traits_detail_IsEqualityComparable::
    IsEqualityComparable;
namespace traits_detail_IsLessThanComparable
{
Ignore operator<(Ignore, Ignore);
template <class T, class U = T>
struct IsLessThanComparable
    : std::is_convertible<
          decltype(std::declval<T>() < std::declval<U>()),
          bool>
{
};
} // namespace traits_detail_IsLessThanComparable
using traits_detail_IsLessThanComparable::
    IsLessThanComparable;
namespace traits_detail_IsNothrowSwappable
{
template <typename T>
using IsNothrowSwappable = std::is_nothrow_swappable<T>;
} // namespace traits_detail_IsNothrowSwappable
using traits_detail_IsNothrowSwappable::IsNothrowSwappable;
template <class T>
struct IsRelocatable
    : std::conditional<
          is_detected_v<traits_detail::detect_IsRelocatable, T>,
          traits_detail::has_true_IsRelocatable<T>,
          is_trivially_copyable<T>>::type
{
};
template <class T>
struct IsZeroInitializable
    : std::conditional<
          is_detected_v<traits_detail::detect_IsZeroInitializable, T>,
          traits_detail::has_true_IsZeroInitializable<T>,
          bool_constant<!std::is_class<T>::value>>::type
{
};
namespace detail
{
template <bool>
struct conditional_;
template <>
struct conditional_<false>
{
  template <typename, typename T>
  using apply = T;
};
template <>
struct conditional_<true>
{
  template <typename T, typename>
  using apply = T;
};
} // namespace detail
template <bool V, typename T, typename F>
using conditional_t = typename detail::conditional_<V>::template apply<T, F>;
template <typename...>
struct Conjunction : std::true_type
{
};
template <typename T>
struct Conjunction<T> : T
{
};
template <typename T, typename... TList>
struct Conjunction<T, TList...>
    : std::conditional<T::value, Conjunction<TList...>, T>::type
{
};
template <typename...>
struct Disjunction : std::false_type
{
};
template <typename T>
struct Disjunction<T> : T
{
};
template <typename T, typename... TList>
struct Disjunction<T, TList...>
    : std::conditional<T::value, T, Disjunction<TList...>>::type
{
};
template <typename T>
struct Negation : bool_constant<!T::value>
{
};
template <bool... Bs>
struct Bools
{
  using valid_type = bool;
  static constexpr std::size_t size()
  {
    return sizeof...(Bs);
  }
};
template <class... Ts>
struct StrictConjunction
    : std::is_same<Bools<Ts::value...>, Bools<(Ts::value || true)...>>
{
};
template <class... Ts>
struct StrictDisjunction
    : Negation<
          std::is_same<Bools<Ts::value...>, Bools<(Ts::value && false)...>>>
{
};
namespace detail
{
template <typename T>
using is_transparent_ = typename T::is_transparent;
}
template <typename T>
inline constexpr bool is_transparent_v =
    is_detected_v<detail::is_transparent_, T>;
template <typename T>
struct is_transparent : bool_constant<is_transparent_v<T>>
{
};
} // namespace folly
namespace folly
{
template <class T, class U>
struct IsRelocatable<std::pair<T, U>>
    : bool_constant<IsRelocatable<T>::value && IsRelocatable<U>::value>
{
};
template <typename T, typename... Ts>
using IsOneOf = StrictDisjunction<std::is_same<T, Ts>...>;
template <typename T>
constexpr bool is_negative(T x)
{
  return std::is_signed<T>::value && x < T(0);
}
template <typename T>
constexpr bool is_non_positive(T x)
{
  return !x || folly::is_negative(x);
}
template <typename T>
constexpr bool is_positive(T x)
{
  return !is_non_positive(x);
}
template <typename T>
constexpr bool is_non_negative(T x)
{
  return !x || is_positive(x);
}
namespace detail
{
template <typename RHS, RHS rhs, typename LHS>
bool less_than_impl(LHS const lhs)
{
  return
      (!std::is_signed<RHS>::value && is_negative(lhs)) ? true :
      (!std::is_signed<LHS>::value && is_negative(rhs)) ? false
      :
      rhs > std::numeric_limits<LHS>::max() ? true
      :
      rhs <= std::numeric_limits<LHS>::min() ? false
                                             :
                                             lhs < rhs;
}
template <typename RHS, RHS rhs, typename LHS>
bool greater_than_impl(LHS const lhs)
{
  return
      (!std::is_signed<RHS>::value && is_negative(lhs)) ? false :
      (!std::is_signed<LHS>::value && is_negative(rhs)) ? true
      :
      rhs > std::numeric_limits<LHS>::max() ? false
      :
      rhs < std::numeric_limits<LHS>::min() ? true
                                            :
                                            lhs > rhs;
}
} // namespace detail
template <typename RHS, RHS rhs, typename LHS>
bool less_than(LHS const lhs)
{
  return detail::
      less_than_impl<RHS, rhs, typename std::remove_reference<LHS>::type>(lhs);
}
template <typename RHS, RHS rhs, typename LHS>
bool greater_than(LHS const lhs)
{
  return detail::
      greater_than_impl<RHS, rhs, typename std::remove_reference<LHS>::type>(
          lhs);
}
} // namespace folly
namespace folly
{
template <class T1, class T2>
struct IsRelocatable<std::unique_ptr<T1, T2>> : std::true_type
{
};
} // namespace folly
namespace folly
{
template <class T1>
struct IsRelocatable<std::shared_ptr<T1>> : std::true_type
{
};
} // namespace folly
namespace folly
{
template <typename Ex>
[[noreturn]] __attribute__((__noinline__)) __attribute__((__cold__)) void throw_exception(Ex &&ex)
{
  throw static_cast<Ex &&>(ex);
}
template <typename Ex>
[[noreturn]] __attribute__((__noinline__)) __attribute__((__cold__)) void terminate_with(Ex &&ex) noexcept
{
  throw_exception(static_cast<Ex &&>(ex));
}
namespace detail
{
struct throw_exception_arg_array_
{
  template <typename R>
  using v = std::remove_extent_t<std::remove_reference_t<R>>;
  template <typename R>
  using apply = std::enable_if_t<std::is_same<char const, v<R>>::value, v<R> *>;
};
struct throw_exception_arg_trivial_
{
  template <typename R>
  using apply = remove_cvref_t<R>;
};
struct throw_exception_arg_base_
{
  template <typename R>
  using apply = R;
};
template <typename R>
using throw_exception_arg_ =
    conditional_t<
        std::is_array<std::remove_reference_t<R>>::value,
        throw_exception_arg_array_,
        conditional_t<
            is_trivially_copyable_v<remove_cvref_t<R>>,
            throw_exception_arg_trivial_,
            throw_exception_arg_base_>>;
template <typename R>
using throw_exception_arg_t =
    typename throw_exception_arg_<R>::template apply<R>;
template <typename Ex, typename... Args>
[[noreturn]] __attribute__((__noinline__)) __attribute__((__cold__)) void throw_exception_(Args... args)
{
  throw_exception(Ex(static_cast<Args>(args)...));
}
template <typename Ex, typename... Args>
[[noreturn]] __attribute__((__noinline__)) __attribute__((__cold__)) void terminate_with_(
    Args... args) noexcept
{
  throw_exception(Ex(static_cast<Args>(args)...));
}
} // namespace detail
template <typename Ex, typename... Args>
[[noreturn]] inline __attribute__((__always_inline__)) __attribute__((__visibility__("hidden"))) void throw_exception(Args &&...args)
{
  detail::throw_exception_<Ex, detail::throw_exception_arg_t<Args &&>...>(
      static_cast<Args &&>(args)...);
}
template <typename Ex, typename... Args>
[[noreturn]] inline __attribute__((__always_inline__)) __attribute__((__visibility__("hidden"))) void terminate_with(Args &&...args)
{
  detail::terminate_with_<Ex, detail::throw_exception_arg_t<Args>...>(
      static_cast<Args &&>(args)...);
}
template <typename F, typename... A>
__attribute__((__noinline__)) __attribute__((__cold__)) auto invoke_cold(F &&f, A &&...a)
    -> decltype(static_cast<F &&>(f)(static_cast<A &&>(a)...))
{
  return static_cast<F &&>(f)(static_cast<A &&>(a)...);
}
template <typename F, typename... A>
[[noreturn]] __attribute__((__noinline__)) __attribute__((__cold__)) void invoke_noreturn_cold(
    F &&f, A &&...a)
{
  static_cast<F &&>(f)(static_cast<A &&>(a)...);
  std::terminate();
}
template <typename E, typename Try, typename Catch, typename... CatchA>
inline __attribute__((__always_inline__)) __attribute__((__visibility__("hidden"))) auto catch_exception(Try &&t, Catch &&c, CatchA &&...a) ->
    typename std::common_type<
        decltype(static_cast<Try &&>(t)()),
        decltype(static_cast<Catch &&>(c)(
            std::declval<E>(), static_cast<CatchA &&>(a)...))>::type
{
  try
  {
    return static_cast<Try &&>(t)();
  }
  catch (E e)
  {
    return invoke_cold(static_cast<Catch &&>(c), e, static_cast<CatchA &&>(a)...);
  }
}
template <typename Try, typename Catch, typename... CatchA>
inline __attribute__((__always_inline__)) __attribute__((__visibility__("hidden"))) auto catch_exception(Try &&t, Catch &&c, CatchA &&...a) ->
    typename std::common_type<
        decltype(static_cast<Try &&>(t)()),
        decltype(static_cast<Catch &&>(c)(static_cast<CatchA &&>(a)...))>::type
{
  try
  {
    return static_cast<Try &&>(t)();
  }
  catch (...)
  {
    return invoke_cold(static_cast<Catch &&>(c), static_cast<CatchA &&>(a)...);
  }
}
[[noreturn]] inline __attribute__((__always_inline__)) __attribute__((__visibility__("hidden"))) void rethrow_current_exception()
{
  throw;
}
} // namespace folly
namespace folly
{
namespace detail
{
template <
    typename Char,
    std::size_t = __builtin_strlen(static_cast<const Char *>(""))>
constexpr std::size_t constexpr_strlen_internal(const Char *s, int) noexcept
{
  return __builtin_strlen(s);
}
template <typename Char>
constexpr std::size_t constexpr_strlen_internal(
    const Char *s, unsigned) noexcept
{
  std::size_t ret = 0;
  while (*s++)
  {
    ++ret;
  }
  return ret;
}
template <typename Char>
constexpr std::size_t constexpr_strlen_fallback(const Char *s) noexcept
{
  return constexpr_strlen_internal(s, 0u);
}
static_assert(
    constexpr_strlen_fallback("123456789") == 9,
    "Someone appears to have broken constexpr_strlen...");
template <
    typename Char,
    int = __builtin_strcmp(static_cast<const Char *>(""), "")>
constexpr int constexpr_strcmp_internal(
    const Char *s1, const Char *s2, int) noexcept
{
  return __builtin_strcmp(s1, s2);
}
template <typename Char>
constexpr int constexpr_strcmp_internal(
    const Char *s1, const Char *s2, unsigned) noexcept
{
  while (*s1 && *s1 == *s2)
  {
    ++s1, ++s2;
  }
  return int(*s2 < *s1) - int(*s1 < *s2);
}
template <typename Char>
constexpr int constexpr_strcmp_fallback(
    const Char *s1, const Char *s2) noexcept
{
  return constexpr_strcmp_internal(s1, s2, 0u);
}
} // namespace detail
template <typename Char>
constexpr std::size_t constexpr_strlen(const Char *s) noexcept
{
  return detail::constexpr_strlen_internal(s, 0);
}
template <typename Char>
constexpr int constexpr_strcmp(const Char *s1, const Char *s2) noexcept
{
  return detail::constexpr_strcmp_internal(s1, s2, 0);
}
} // namespace folly
namespace folly
{
class CpuId
{
public:
  inline __attribute__((__always_inline__)) CpuId()
  {
    uint32_t n;
    __asm__("cpuid"
            : "=a"(n)
            : "a"(0)
            : "ebx", "ecx", "edx");
    if (n >= 1)
    {
      uint32_t f1a;
      __asm__("cpuid"
              : "=a"(f1a), "=c"(f1c_), "=d"(f1d_)
              : "a"(1)
              : "ebx");
    }
    if (n >= 7)
    {
      uint32_t f7a;
      __asm__("cpuid"
              : "=a"(f7a), "=b"(f7b_), "=c"(f7c_)
              : "a"(7), "c"(0)
              : "edx");
    }
  }
  inline __attribute__((__always_inline__)) bool sse3() const
  {
    return ((f1c_) & (1U << 0)) != 0;
  }
  inline __attribute__((__always_inline__)) bool pclmuldq() const
  {
    return ((f1c_) & (1U << 1)) != 0;
  }
  inline __attribute__((__always_inline__)) bool dtes64() const
  {
    return ((f1c_) & (1U << 2)) != 0;
  }
  inline __attribute__((__always_inline__)) bool monitor() const
  {
    return ((f1c_) & (1U << 3)) != 0;
  }
  inline __attribute__((__always_inline__)) bool dscpl() const
  {
    return ((f1c_) & (1U << 4)) != 0;
  }
  inline __attribute__((__always_inline__)) bool vmx() const
  {
    return ((f1c_) & (1U << 5)) != 0;
  }
  inline __attribute__((__always_inline__)) bool smx() const
  {
    return ((f1c_) & (1U << 6)) != 0;
  }
  inline __attribute__((__always_inline__)) bool eist() const
  {
    return ((f1c_) & (1U << 7)) != 0;
  }
  inline __attribute__((__always_inline__)) bool tm2() const
  {
    return ((f1c_) & (1U << 8)) != 0;
  }
  inline __attribute__((__always_inline__)) bool ssse3() const
  {
    return ((f1c_) & (1U << 9)) != 0;
  }
  inline __attribute__((__always_inline__)) bool cnxtid() const
  {
    return ((f1c_) & (1U << 10)) != 0;
  }
  inline __attribute__((__always_inline__)) bool fma() const
  {
    return ((f1c_) & (1U << 12)) != 0;
  }
  inline __attribute__((__always_inline__)) bool cx16() const
  {
    return ((f1c_) & (1U << 13)) != 0;
  }
  inline __attribute__((__always_inline__)) bool xtpr() const
  {
    return ((f1c_) & (1U << 14)) != 0;
  }
  inline __attribute__((__always_inline__)) bool pdcm() const
  {
    return ((f1c_) & (1U << 15)) != 0;
  }
  inline __attribute__((__always_inline__)) bool pcid() const
  {
    return ((f1c_) & (1U << 17)) != 0;
  }
  inline __attribute__((__always_inline__)) bool dca() const
  {
    return ((f1c_) & (1U << 18)) != 0;
  }
  inline __attribute__((__always_inline__)) bool sse41() const
  {
    return ((f1c_) & (1U << 19)) != 0;
  }
  inline __attribute__((__always_inline__)) bool sse42() const
  {
    return ((f1c_) & (1U << 20)) != 0;
  }
  inline __attribute__((__always_inline__)) bool x2apic() const
  {
    return ((f1c_) & (1U << 21)) != 0;
  }
  inline __attribute__((__always_inline__)) bool movbe() const
  {
    return ((f1c_) & (1U << 22)) != 0;
  }
  inline __attribute__((__always_inline__)) bool popcnt() const
  {
    return ((f1c_) & (1U << 23)) != 0;
  }
  inline __attribute__((__always_inline__)) bool tscdeadline() const
  {
    return ((f1c_) & (1U << 24)) != 0;
  }
  inline __attribute__((__always_inline__)) bool aes() const
  {
    return ((f1c_) & (1U << 25)) != 0;
  }
  inline __attribute__((__always_inline__)) bool xsave() const
  {
    return ((f1c_) & (1U << 26)) != 0;
  }
  inline __attribute__((__always_inline__)) bool osxsave() const
  {
    return ((f1c_) & (1U << 27)) != 0;
  }
  inline __attribute__((__always_inline__)) bool avx() const
  {
    return ((f1c_) & (1U << 28)) != 0;
  }
  inline __attribute__((__always_inline__)) bool f16c() const
  {
    return ((f1c_) & (1U << 29)) != 0;
  }
  inline __attribute__((__always_inline__)) bool rdrand() const
  {
    return ((f1c_) & (1U << 30)) != 0;
  }
  inline __attribute__((__always_inline__)) bool fpu() const
  {
    return ((f1d_) & (1U << 0)) != 0;
  }
  inline __attribute__((__always_inline__)) bool vme() const
  {
    return ((f1d_) & (1U << 1)) != 0;
  }
  inline __attribute__((__always_inline__)) bool de() const
  {
    return ((f1d_) & (1U << 2)) != 0;
  }
  inline __attribute__((__always_inline__)) bool pse() const
  {
    return ((f1d_) & (1U << 3)) != 0;
  }
  inline __attribute__((__always_inline__)) bool tsc() const
  {
    return ((f1d_) & (1U << 4)) != 0;
  }
  inline __attribute__((__always_inline__)) bool msr() const
  {
    return ((f1d_) & (1U << 5)) != 0;
  }
  inline __attribute__((__always_inline__)) bool pae() const
  {
    return ((f1d_) & (1U << 6)) != 0;
  }
  inline __attribute__((__always_inline__)) bool mce() const
  {
    return ((f1d_) & (1U << 7)) != 0;
  }
  inline __attribute__((__always_inline__)) bool cx8() const
  {
    return ((f1d_) & (1U << 8)) != 0;
  }
  inline __attribute__((__always_inline__)) bool apic() const
  {
    return ((f1d_) & (1U << 9)) != 0;
  }
  inline __attribute__((__always_inline__)) bool sep() const
  {
    return ((f1d_) & (1U << 11)) != 0;
  }
  inline __attribute__((__always_inline__)) bool mtrr() const
  {
    return ((f1d_) & (1U << 12)) != 0;
  }
  inline __attribute__((__always_inline__)) bool pge() const
  {
    return ((f1d_) & (1U << 13)) != 0;
  }
  inline __attribute__((__always_inline__)) bool mca() const
  {
    return ((f1d_) & (1U << 14)) != 0;
  }
  inline __attribute__((__always_inline__)) bool cmov() const
  {
    return ((f1d_) & (1U << 15)) != 0;
  }
  inline __attribute__((__always_inline__)) bool pat() const
  {
    return ((f1d_) & (1U << 16)) != 0;
  }
  inline __attribute__((__always_inline__)) bool pse36() const
  {
    return ((f1d_) & (1U << 17)) != 0;
  }
  inline __attribute__((__always_inline__)) bool psn() const
  {
    return ((f1d_) & (1U << 18)) != 0;
  }
  inline __attribute__((__always_inline__)) bool clfsh() const
  {
    return ((f1d_) & (1U << 19)) != 0;
  }
  inline __attribute__((__always_inline__)) bool ds() const
  {
    return ((f1d_) & (1U << 21)) != 0;
  }
  inline __attribute__((__always_inline__)) bool acpi() const
  {
    return ((f1d_) & (1U << 22)) != 0;
  }
  inline __attribute__((__always_inline__)) bool mmx() const
  {
    return ((f1d_) & (1U << 23)) != 0;
  }
  inline __attribute__((__always_inline__)) bool fxsr() const
  {
    return ((f1d_) & (1U << 24)) != 0;
  }
  inline __attribute__((__always_inline__)) bool sse() const
  {
    return ((f1d_) & (1U << 25)) != 0;
  }
  inline __attribute__((__always_inline__)) bool sse2() const
  {
    return ((f1d_) & (1U << 26)) != 0;
  }
  inline __attribute__((__always_inline__)) bool ss() const
  {
    return ((f1d_) & (1U << 27)) != 0;
  }
  inline __attribute__((__always_inline__)) bool htt() const
  {
    return ((f1d_) & (1U << 28)) != 0;
  }
  inline __attribute__((__always_inline__)) bool tm() const
  {
    return ((f1d_) & (1U << 29)) != 0;
  }
  inline __attribute__((__always_inline__)) bool pbe() const
  {
    return ((f1d_) & (1U << 31)) != 0;
  }
  inline __attribute__((__always_inline__)) bool bmi1() const
  {
    return ((f7b_) & (1U << 3)) != 0;
  }
  inline __attribute__((__always_inline__)) bool hle() const
  {
    return ((f7b_) & (1U << 4)) != 0;
  }
  inline __attribute__((__always_inline__)) bool avx2() const
  {
    return ((f7b_) & (1U << 5)) != 0;
  }
  inline __attribute__((__always_inline__)) bool smep() const
  {
    return ((f7b_) & (1U << 7)) != 0;
  }
  inline __attribute__((__always_inline__)) bool bmi2() const
  {
    return ((f7b_) & (1U << 8)) != 0;
  }
  inline __attribute__((__always_inline__)) bool erms() const
  {
    return ((f7b_) & (1U << 9)) != 0;
  }
  inline __attribute__((__always_inline__)) bool invpcid() const
  {
    return ((f7b_) & (1U << 10)) != 0;
  }
  inline __attribute__((__always_inline__)) bool rtm() const
  {
    return ((f7b_) & (1U << 11)) != 0;
  }
  inline __attribute__((__always_inline__)) bool mpx() const
  {
    return ((f7b_) & (1U << 14)) != 0;
  }
  inline __attribute__((__always_inline__)) bool avx512f() const
  {
    return ((f7b_) & (1U << 16)) != 0;
  }
  inline __attribute__((__always_inline__)) bool avx512dq() const
  {
    return ((f7b_) & (1U << 17)) != 0;
  }
  inline __attribute__((__always_inline__)) bool rdseed() const
  {
    return ((f7b_) & (1U << 18)) != 0;
  }
  inline __attribute__((__always_inline__)) bool adx() const
  {
    return ((f7b_) & (1U << 19)) != 0;
  }
  inline __attribute__((__always_inline__)) bool smap() const
  {
    return ((f7b_) & (1U << 20)) != 0;
  }
  inline __attribute__((__always_inline__)) bool avx512ifma() const
  {
    return ((f7b_) & (1U << 21)) != 0;
  }
  inline __attribute__((__always_inline__)) bool pcommit() const
  {
    return ((f7b_) & (1U << 22)) != 0;
  }
  inline __attribute__((__always_inline__)) bool clflushopt() const
  {
    return ((f7b_) & (1U << 23)) != 0;
  }
  inline __attribute__((__always_inline__)) bool clwb() const
  {
    return ((f7b_) & (1U << 24)) != 0;
  }
  inline __attribute__((__always_inline__)) bool avx512pf() const
  {
    return ((f7b_) & (1U << 26)) != 0;
  }
  inline __attribute__((__always_inline__)) bool avx512er() const
  {
    return ((f7b_) & (1U << 27)) != 0;
  }
  inline __attribute__((__always_inline__)) bool avx512cd() const
  {
    return ((f7b_) & (1U << 28)) != 0;
  }
  inline __attribute__((__always_inline__)) bool sha() const
  {
    return ((f7b_) & (1U << 29)) != 0;
  }
  inline __attribute__((__always_inline__)) bool avx512bw() const
  {
    return ((f7b_) & (1U << 30)) != 0;
  }
  inline __attribute__((__always_inline__)) bool avx512vl() const
  {
    return ((f7b_) & (1U << 31)) != 0;
  }
  inline __attribute__((__always_inline__)) bool prefetchwt1() const
  {
    return ((f7c_) & (1U << 0)) != 0;
  }
  inline __attribute__((__always_inline__)) bool avx512vbmi() const
  {
    return ((f7c_) & (1U << 1)) != 0;
  }
  inline __attribute__((__always_inline__)) bool vaes() const
  {
    return ((f7c_) & (1U << 9)) != 0;
  }
  inline __attribute__((__always_inline__)) bool vpclmulqdq() const
  {
    return ((f7c_) & (1U << 10)) != 0;
  }
private:
  uint32_t f1c_ = 0;
  uint32_t f1d_ = 0;
  uint32_t f7b_ = 0;
  uint32_t f7c_ = 0;
};
} // namespace folly
namespace folly
{
namespace detail
{
class StringPieceLite
{
public:
  StringPieceLite(const char *b, const char *e)
      : b_(b), e_(e)
  {
  }
  template <typename Range>
  StringPieceLite(const Range &r)
      : StringPieceLite(r.data(), r.data() + r.size())
  {
  }
  const char *data() const
  {
    return b_;
  }
  const char *begin() const
  {
    return b_;
  }
  const char *end() const
  {
    return e_;
  }
  size_t size() const
  {
    return size_t(e_ - b_);
  }
  bool empty() const
  {
    return size() == 0;
  }
  const char &operator[](size_t i) const
  {
    (static_cast<bool>(
         size() > i
         )
         ? void(0)
         : __assert_fail(
             "size() > i"
             ,
             "../folly/detail/RangeCommon.h", 48, __extension__ __PRETTY_FUNCTION__))
        ;
    return b_[i];
  }
  template <typename Range>
  explicit operator Range() const
  {
    return Range(begin(), end());
  }
private:
  const char *b_;
  const char *e_;
};
inline size_t qfind_first_byte_of_std(
    const StringPieceLite haystack, const StringPieceLite needles)
{
  auto ret = std::find_first_of(
      haystack.begin(),
      haystack.end(),
      needles.begin(),
      needles.end(),
      [](char a, char b) { return a == b; });
  return ret == haystack.end() ? std::string::npos : ret - haystack.begin();
}
size_t qfind_first_byte_of_bitset(
    const StringPieceLite haystack, const StringPieceLite needles);
size_t qfind_first_byte_of_byteset(
    const StringPieceLite haystack, const StringPieceLite needles);
inline size_t qfind_first_byte_of_nosse(
    const StringPieceLite haystack, const StringPieceLite needles)
{
  if ((__builtin_expect((needles.empty() || haystack.empty()), 0)))
  {
    return std::string::npos;
  }
  if ((needles.size() >= 4 && haystack.size() <= 10) ||
      (needles.size() >= 16 && haystack.size() <= 64) || needles.size() >= 32)
  {
    return qfind_first_byte_of_byteset(haystack, needles);
  }
  return qfind_first_byte_of_std(haystack, needles);
}
} // namespace detail
} // namespace folly
namespace folly
{
namespace detail
{
size_t qfind_first_byte_of_sse42(
    const StringPieceLite haystack, const StringPieceLite needles);
}
} // namespace folly
namespace folly
{
template <class T>
struct IsSomeString : std::false_type
{
};
template <typename Alloc>
struct IsSomeString<std::basic_string<char, std::char_traits<char>, Alloc>>
    : std::true_type
{
};
template <class Iter>
class Range;
template <
    class Iter,
    class Comp = std::equal_to<typename Range<Iter>::value_type>>
inline size_t qfind(
    const Range<Iter> &haystack, const Range<Iter> &needle, Comp eq = Comp());
template <class Iter>
size_t qfind(
    const Range<Iter> &haystack,
    const typename Range<Iter>::value_type &needle);
template <class Iter>
size_t rfind(
    const Range<Iter> &haystack,
    const typename Range<Iter>::value_type &needle);
template <class Iter>
inline size_t qfind_first_of(
    const Range<Iter> &haystack, const Range<Iter> &needle);
namespace detail
{
template <class T>
struct IsCharPointer
{
};
template <>
struct IsCharPointer<char *>
{
  typedef int type;
};
template <>
struct IsCharPointer<const char *>
{
  typedef int const_type;
  typedef int type;
};
} // namespace detail
template <class Iter>
class Range
{
private:
  template <typename Alloc>
  using string = std::basic_string<char, std::char_traits<char>, Alloc>;
public:
  typedef std::size_t size_type;
  typedef Iter iterator;
  typedef Iter const_iterator;
  typedef typename std::remove_reference<
      typename std::iterator_traits<Iter>::reference>::type value_type;
  using difference_type = typename std::iterator_traits<Iter>::difference_type;
  typedef typename std::iterator_traits<Iter>::reference reference;
  typedef typename std::conditional<
      std::is_same<Iter, char *>::value ||
          std::is_same<Iter, unsigned char *>::value,
      Range<const value_type *>,
      Range<Iter>>::type const_range_type;
  typedef std::char_traits<typename std::remove_const<value_type>::type>
      traits_type;
  static const size_type npos;
  constexpr Range()
      : b_(), e_()
  {
  }
  constexpr Range(const Range &) = default;
  constexpr Range(Range &&) = default;
public:
  constexpr Range(Iter start, Iter end)
      : b_(start), e_(end)
  {
  }
  constexpr Range(Iter start, size_t size)
      : b_(start), e_(start + size)
  {
  }
  Range(std::nullptr_t) = delete;
  constexpr Range(Iter str)
      : b_(str), e_(str + constexpr_strlen(str))
  {
    static_assert(
        std::is_same<int, typename detail::IsCharPointer<Iter>::type>::value,
        "This constructor is only available for character ranges");
  }
  template <
      class Alloc,
      class T = Iter,
      typename detail::IsCharPointer<T>::const_type = 0>
  Range(const string<Alloc> &str)
      : b_(str.data()), e_(b_ + str.size())
  {
  }
  template <
      class Alloc,
      class T = Iter,
      typename detail::IsCharPointer<T>::const_type = 0>
  Range(const string<Alloc> &str, typename string<Alloc>::size_type startFrom)
  {
    if ((__builtin_expect((startFrom > str.size()), 0)))
    {
      throw_exception<std::out_of_range>("index out of range");
    }
    b_ = str.data() + startFrom;
    e_ = str.data() + str.size();
  }
  template <
      class Alloc,
      class T = Iter,
      typename detail::IsCharPointer<T>::const_type = 0>
  Range(
      const string<Alloc> &str,
      typename string<Alloc>::size_type startFrom,
      typename string<Alloc>::size_type size)
  {
    if ((__builtin_expect((startFrom > str.size()), 0)))
    {
      throw_exception<std::out_of_range>("index out of range");
    }
    b_ = str.data() + startFrom;
    if (str.size() - startFrom < size)
    {
      e_ = str.data() + str.size();
    }
    else
    {
      e_ = b_ + size;
    }
  }
  Range(const Range &other, size_type first, size_type length = npos)
      : Range(other.subpiece(first, length))
  {
  }
  template <
      class Container,
      class = typename std::enable_if<
          std::is_same<Iter, typename Container::const_pointer>::value>::type,
      class = decltype(
          Iter(std::declval<Container const &>().data()),
          Iter(
              std::declval<Container const &>().data() +
              std::declval<Container const &>().size()))>
  constexpr Range(Container const &container)
      : Range(container.data(), container.size())
  {
  }
  template <
      class Container,
      class = typename std::enable_if<
          std::is_same<Iter, typename Container::const_pointer>::value>::type,
      class = decltype(
          Iter(std::declval<Container const &>().data()),
          Iter(
              std::declval<Container const &>().data() +
              std::declval<Container const &>().size()))>
  Range(Container const &container, typename Container::size_type startFrom)
  {
    auto const cdata = container.data();
    auto const csize = container.size();
    if ((__builtin_expect((startFrom > csize), 0)))
    {
      throw_exception<std::out_of_range>("index out of range");
    }
    b_ = cdata + startFrom;
    e_ = cdata + csize;
  }
  template <
      class Container,
      class = typename std::enable_if<
          std::is_same<Iter, typename Container::const_pointer>::value>::type,
      class = decltype(
          Iter(std::declval<Container const &>().data()),
          Iter(
              std::declval<Container const &>().data() +
              std::declval<Container const &>().size()))>
  Range(
      Container const &container,
      typename Container::size_type startFrom,
      typename Container::size_type size)
  {
    auto const cdata = container.data();
    auto const csize = container.size();
    if ((__builtin_expect((startFrom > csize), 0)))
    {
      throw_exception<std::out_of_range>("index out of range");
    }
    b_ = cdata + startFrom;
    if (csize - startFrom < size)
    {
      e_ = cdata + csize;
    }
    else
    {
      e_ = b_ + size;
    }
  }
  template <
      class OtherIter,
      typename std::enable_if<
          (std::is_same<Iter, const unsigned char *>::value &&
           (std::is_same<OtherIter, const char *>::value ||
            std::is_same<OtherIter, char *>::value)),
          int>::type
      = 0>
  Range(const Range<OtherIter> &other)
      : b_(reinterpret_cast<const unsigned char *>(other.begin())),
        e_(reinterpret_cast<const unsigned char *>(other.end()))
  {
  }
  template <
      class OtherIter,
      typename std::enable_if<
          (std::is_same<Iter, unsigned char *>::value &&
           std::is_same<OtherIter, char *>::value),
          int>::type
      = 0>
  Range(const Range<OtherIter> &other)
      : b_(reinterpret_cast<unsigned char *>(other.begin())),
        e_(reinterpret_cast<unsigned char *>(other.end()))
  {
  }
  template <
      class OtherIter,
      typename std::enable_if<
          (std::is_same<Iter, const char *>::value &&
           (std::is_same<OtherIter, const unsigned char *>::value ||
            std::is_same<OtherIter, unsigned char *>::value)),
          int>::type
      = 0>
  explicit Range(const Range<OtherIter> &other)
      : b_(reinterpret_cast<const char *>(other.begin())),
        e_(reinterpret_cast<const char *>(other.end()))
  {
  }
  template <
      class OtherIter,
      typename std::enable_if<
          (std::is_same<Iter, char *>::value &&
           std::is_same<OtherIter, unsigned char *>::value),
          int>::type
      = 0>
  explicit Range(const Range<OtherIter> &other)
      : b_(reinterpret_cast<char *>(other.begin())),
        e_(reinterpret_cast<char *>(other.end()))
  {
  }
  template <
      class OtherIter,
      typename std::enable_if<
          (!std::is_same<Iter, OtherIter>::value &&
           std::is_convertible<OtherIter, Iter>::value),
          int>::type
      = 0>
  constexpr Range(const Range<OtherIter> &other)
      : b_(other.begin()), e_(other.end())
  {
  }
  template <
      class OtherIter,
      typename std::enable_if<
          (!std::is_same<Iter, OtherIter>::value &&
           !std::is_convertible<OtherIter, Iter>::value &&
           std::is_constructible<Iter, const OtherIter &>::value),
          int>::type
      = 0>
  constexpr explicit Range(const Range<OtherIter> &other)
      : b_(other.begin()), e_(other.end())
  {
  }
  template <
      class T,
      size_t N,
      typename = typename std::enable_if<
          std::is_convertible<const T *, Iter>::value>::type>
  constexpr explicit Range(const std::array<T, N> &array)
      : b_{array.empty() ? nullptr : &array.at(0)},
        e_{array.empty() ? nullptr : &array.at(0) + N}
  {
  }
  template <
      class T,
      size_t N,
      typename =
          typename std::enable_if<std::is_convertible<T *, Iter>::value>::type>
  constexpr explicit Range(std::array<T, N> &array)
      : b_{array.empty() ? nullptr : &array.at(0)},
        e_{array.empty() ? nullptr : &array.at(0) + N}
  {
  }
  Range &operator=(const Range &rhs) & = default;
  Range &operator=(Range &&rhs) & = default;
  template <
      class Alloc,
      class T = Iter,
      typename detail::IsCharPointer<T>::const_type = 0>
  Range &operator=(string<Alloc> &&rhs) = delete;
  void clear()
  {
    b_ = Iter();
    e_ = Iter();
  }
  void assign(Iter start, Iter end)
  {
    b_ = start;
    e_ = end;
  }
  void reset(Iter start, size_type size)
  {
    b_ = start;
    e_ = start + size;
  }
  template <typename Alloc>
  void reset(const string<Alloc> &str)
  {
    reset(str.data(), str.size());
  }
  constexpr size_type size() const
  {
    (static_cast<bool>(
         b_ <= e_
         )
         ? void(0)
         : __assert_fail(
             "b_ <= e_"
             ,
             "../folly/Range.h", 424, __extension__ __PRETTY_FUNCTION__))
        ;
    return size_type(e_ - b_);
  }
  constexpr size_type walk_size() const
  {
    return size_type(std::distance(b_, e_));
  }
  constexpr bool empty() const
  {
    return b_ == e_;
  }
  constexpr Iter data() const
  {
    return b_;
  }
  constexpr Iter start() const
  {
    return b_;
  }
  constexpr Iter begin() const
  {
    return b_;
  }
  constexpr Iter end() const
  {
    return e_;
  }
  constexpr Iter cbegin() const
  {
    return b_;
  }
  constexpr Iter cend() const
  {
    return e_;
  }
  value_type &front()
  {
    (static_cast<bool>(
         b_ < e_
         )
         ? void(0)
         : __assert_fail(
             "b_ < e_"
             ,
             "../folly/Range.h", 439, __extension__ __PRETTY_FUNCTION__))
        ;
    return *b_;
  }
  value_type &back()
  {
    (static_cast<bool>(
         b_ < e_
         )
         ? void(0)
         : __assert_fail(
             "b_ < e_"
             ,
             "../folly/Range.h", 443, __extension__ __PRETTY_FUNCTION__))
        ;
    return *std::prev(e_);
  }
  const value_type &front() const
  {
    (static_cast<bool>(
         b_ < e_
         )
         ? void(0)
         : __assert_fail(
             "b_ < e_"
             ,
             "../folly/Range.h", 447, __extension__ __PRETTY_FUNCTION__))
        ;
    return *b_;
  }
  const value_type &back() const
  {
    (static_cast<bool>(
         b_ < e_
         )
         ? void(0)
         : __assert_fail(
             "b_ < e_"
             ,
             "../folly/Range.h", 451, __extension__ __PRETTY_FUNCTION__))
        ;
    return *std::prev(e_);
  }
private:
  struct NotStringView
  {
  };
  template <typename ValueType>
  struct StringViewType
      : std::conditional<
            std::is_pod<std::remove_const_t<ValueType>>::value,
            std::basic_string_view<std::remove_const_t<ValueType>>,
            NotStringView>
  {
  };
  template <typename Target>
  struct IsConstructibleViaStringView
      : Conjunction<
            std::is_constructible<
                _t<StringViewType<value_type>>,
                Iter const &,
                size_type>,
            std::is_constructible<Target, _t<StringViewType<value_type>>>>
  {
  };
public:
  template <
      typename Tgt,
      std::enable_if_t<
          std::is_constructible<Tgt, Iter const &, size_type>::value &&
              !IsConstructibleViaStringView<Tgt>::value,
          int> = 0>
  constexpr explicit operator Tgt() const noexcept(
      std::is_nothrow_constructible<Tgt, Iter const &, size_type>::value)
  {
    return Tgt(b_, walk_size());
  }
  template <
      typename Tgt,
      std::enable_if_t<
          !std::is_constructible<Tgt, Iter const &, size_type>::value &&
              std::is_constructible<Tgt, Iter const &, Iter const &>::value &&
              !IsConstructibleViaStringView<Tgt>::value,
          int> = 0>
  constexpr explicit operator Tgt() const noexcept(
      std::is_nothrow_constructible<Tgt, Iter const &, Iter const &>::value)
  {
    return Tgt(b_, e_);
  }
  template <
      typename Tgt,
      typename ValueType = value_type,
      std::enable_if_t<
          StrictConjunction<
              std::is_same<Tgt, _t<StringViewType<ValueType>>>,
              std::is_constructible<
                  _t<StringViewType<ValueType>>,
                  Iter const &,
                  size_type>>::value,
          int> = 0>
  constexpr operator Tgt() const noexcept(
      std::is_nothrow_constructible<Tgt, Iter const &, size_type>::value)
  {
    return Tgt(b_, walk_size());
  }
  template <typename Tgt, typename... Args>
  constexpr std::enable_if_t<
      std::is_constructible<Tgt, Iter const &, size_type>::value,
      Tgt>
  to(Args &&...args) const noexcept(
      std::is_nothrow_constructible<Tgt, Iter const &, size_type, Args &&...>::
          value)
  {
    return Tgt(b_, walk_size(), static_cast<Args &&>(args)...);
  }
  template <typename Tgt, typename... Args>
  constexpr std::enable_if_t<
      !std::is_constructible<Tgt, Iter const &, size_type>::value &&
          std::is_constructible<Tgt, Iter const &, Iter const &>::value,
      Tgt>
  to(Args &&...args) const noexcept(
      std::is_nothrow_constructible<Tgt, Iter const &, Iter const &, Args &&...>::
          value)
  {
    return Tgt(b_, e_, static_cast<Args &&>(args)...);
  }
  std::string str() const
  {
    return to<std::string>();
  }
  std::string toString() const
  {
    return to<std::string>();
  }
  const_range_type castToConst() const
  {
    return const_range_type(*this);
  }
  int compare(const const_range_type &o) const
  {
    const size_type tsize = this->size();
    const size_type osize = o.size();
    const size_type msize = std::min(tsize, osize);
    int r = traits_type::compare(data(), o.data(), msize);
    if (r == 0 && tsize != osize)
    {
      r = (static_cast<int>((osize - tsize) >> (8 * sizeof(size_t) - 1))
           << 1)
          -
          1;
    }
    return r;
  }
  value_type &operator[](size_t i)
  {
    (static_cast<bool>(
         i < size()
             )
         ? void(0)
         : __assert_fail(
             "i < size()"
             ,
             "../folly/Range.h", 599, __extension__ __PRETTY_FUNCTION__))
        ;
    return b_[i];
  }
  const value_type &operator[](size_t i) const
  {
    (static_cast<bool>(
         i < size()
             )
         ? void(0)
         : __assert_fail(
             "i < size()"
             ,
             "../folly/Range.h", 604, __extension__ __PRETTY_FUNCTION__))
        ;
    return b_[i];
  }
  value_type &at(size_t i)
  {
    if (i >= size())
    {
      throw_exception<std::out_of_range>("index out of range");
    }
    return b_[i];
  }
  const value_type &at(size_t i) const
  {
    if (i >= size())
    {
      throw_exception<std::out_of_range>("index out of range");
    }
    return b_[i];
  }
  [[deprecated(
      "Replace with folly::Hash if the hash is not serialized")]] uint32_t
  hash() const
  {
    uint32_t hash = 5381;
    for (size_t ix = 0; ix < size(); ix++)
    {
      hash = ((hash << 5) + hash) + b_[ix];
    }
    return hash;
  }
  void advance(size_type n)
  {
    if ((__builtin_expect((n > size()), 0)))
    {
      throw_exception<std::out_of_range>("index out of range");
    }
    b_ += n;
  }
  void subtract(size_type n)
  {
    if ((__builtin_expect((n > size()), 0)))
    {
      throw_exception<std::out_of_range>("index out of range");
    }
    e_ -= n;
  }
  Range subpiece(size_type first, size_type length = npos) const
  {
    if ((__builtin_expect((first > size()), 0)))
    {
      throw_exception<std::out_of_range>("index out of range");
    }
    return Range(b_ + first, std::min(length, size() - first));
  }
  void uncheckedAdvance(size_type n)
  {
    (static_cast<bool>(
         n <= size()
             )
         ? void(0)
         : __assert_fail(
             "n <= size()"
             ,
             "../folly/Range.h", 676, __extension__ __PRETTY_FUNCTION__))
        ;
    b_ += n;
  }
  void uncheckedSubtract(size_type n)
  {
    (static_cast<bool>(
         n <= size()
             )
         ? void(0)
         : __assert_fail(
             "n <= size()"
             ,
             "../folly/Range.h", 681, __extension__ __PRETTY_FUNCTION__))
        ;
    e_ -= n;
  }
  Range uncheckedSubpiece(size_type first, size_type length = npos) const
  {
    (static_cast<bool>(
         first <= size()
             )
         ? void(0)
         : __assert_fail(
             "first <= size()"
             ,
             "../folly/Range.h", 686, __extension__ __PRETTY_FUNCTION__))
        ;
    return Range(b_ + first, std::min(length, size() - first));
  }
  void pop_front()
  {
    (static_cast<bool>(
         b_ < e_
         )
         ? void(0)
         : __assert_fail(
             "b_ < e_"
             ,
             "../folly/Range.h", 691, __extension__ __PRETTY_FUNCTION__))
        ;
    ++b_;
  }
  void pop_back()
  {
    (static_cast<bool>(
         b_ < e_
         )
         ? void(0)
         : __assert_fail(
             "b_ < e_"
             ,
             "../folly/Range.h", 696, __extension__ __PRETTY_FUNCTION__))
        ;
    --e_;
  }
  size_type find(const_range_type str) const
  {
    return qfind(castToConst(), str);
  }
  size_type find(const_range_type str, size_t pos) const
  {
    if (pos > size())
    {
      return std::string::npos;
    }
    size_t ret = qfind(castToConst().subpiece(pos), str);
    return ret == npos ? ret : ret + pos;
  }
  size_type find(Iter s, size_t pos, size_t n) const
  {
    if (pos > size())
    {
      return std::string::npos;
    }
    auto forFinding = castToConst();
    size_t ret = qfind(
        pos ? forFinding.subpiece(pos) : forFinding, const_range_type(s, n));
    return ret == npos ? ret : ret + pos;
  }
  size_type find(const Iter s) const
  {
    return qfind(castToConst(), const_range_type(s));
  }
  size_type find(const Iter s, size_t pos) const
  {
    if (pos > size())
    {
      return std::string::npos;
    }
    size_type ret = qfind(castToConst().subpiece(pos), const_range_type(s));
    return ret == npos ? ret : ret + pos;
  }
  size_type find(value_type c) const
  {
    return qfind(castToConst(), c);
  }
  size_type rfind(value_type c) const
  {
    return folly::rfind(castToConst(), c);
  }
  size_type find(value_type c, size_t pos) const
  {
    if (pos > size())
    {
      return std::string::npos;
    }
    size_type ret = qfind(castToConst().subpiece(pos), c);
    return ret == npos ? ret : ret + pos;
  }
  size_type find_first_of(const_range_type needles) const
  {
    return qfind_first_of(castToConst(), needles);
  }
  size_type find_first_of(const_range_type needles, size_t pos) const
  {
    if (pos > size())
    {
      return std::string::npos;
    }
    size_type ret = qfind_first_of(castToConst().subpiece(pos), needles);
    return ret == npos ? ret : ret + pos;
  }
  size_type find_first_of(Iter needles) const
  {
    return find_first_of(const_range_type(needles));
  }
  size_type find_first_of(Iter needles, size_t pos) const
  {
    return find_first_of(const_range_type(needles), pos);
  }
  size_type find_first_of(Iter needles, size_t pos, size_t n) const
  {
    return find_first_of(const_range_type(needles, n), pos);
  }
  size_type find_first_of(value_type c) const
  {
    return find(c);
  }
  size_type find_first_of(value_type c, size_t pos) const
  {
    return find(c, pos);
  }
  bool contains(const const_range_type &other) const
  {
    return find(other) != std::string::npos;
  }
  bool contains(const value_type &other) const
  {
    return find(other) != std::string::npos;
  }
  void swap(Range &rhs)
  {
    std::swap(b_, rhs.b_);
    std::swap(e_, rhs.e_);
  }
  bool startsWith(const const_range_type &other) const
  {
    return size() >= other.size() &&
           castToConst().subpiece(0, other.size()) == other;
  }
  bool startsWith(value_type c) const
  {
    return !empty() && front() == c;
  }
  template <class Comp>
  bool startsWith(const const_range_type &other, Comp &&eq) const
  {
    if (size() < other.size())
    {
      return false;
    }
    auto const trunc = subpiece(0, other.size());
    return std::equal(
        trunc.begin(), trunc.end(), other.begin(), std::forward<Comp>(eq));
  }
  bool endsWith(const const_range_type &other) const
  {
    return size() >= other.size() &&
           castToConst().subpiece(size() - other.size()) == other;
  }
  bool endsWith(value_type c) const
  {
    return !empty() && back() == c;
  }
  template <class Comp>
  bool endsWith(const const_range_type &other, Comp &&eq) const
  {
    if (size() < other.size())
    {
      return false;
    }
    auto const trunc = subpiece(size() - other.size());
    return std::equal(
        trunc.begin(), trunc.end(), other.begin(), std::forward<Comp>(eq));
  }
  template <class Comp>
  bool equals(const const_range_type &other, Comp &&eq) const
  {
    return size() == other.size() &&
           std::equal(begin(), end(), other.begin(), std::forward<Comp>(eq));
  }
  void erase(Iter b, Iter e)
  {
    if (b == b_)
    {
      b_ = e;
    }
    else if (e == e_)
    {
      e_ = b;
    }
    else
    {
      throw_exception<std::out_of_range>("index out of range");
    }
  }
  bool removePrefix(const const_range_type &prefix)
  {
    return startsWith(prefix) && (b_ += prefix.size(), true);
  }
  bool removePrefix(value_type prefix)
  {
    return startsWith(prefix) && (++b_, true);
  }
  bool removeSuffix(const const_range_type &suffix)
  {
    return endsWith(suffix) && (e_ -= suffix.size(), true);
  }
  bool removeSuffix(value_type suffix)
  {
    return endsWith(suffix) && (--e_, true);
  }
  bool replaceAt(size_t pos, const_range_type replacement)
  {
    if (size() < pos + replacement.size())
    {
      return false;
    }
    std::copy(replacement.begin(), replacement.end(), begin() + pos);
    return true;
  }
  size_t replaceAll(const_range_type source, const_range_type dest)
  {
    if (source.size() != dest.size())
    {
      throw_exception<std::invalid_argument>(
          "replacement must have the same size as source");
    }
    if (dest.empty())
    {
      return 0;
    }
    size_t pos = 0;
    size_t num_replaced = 0;
    size_type found = std::string::npos;
    while ((found = find(source, pos)) != std::string::npos)
    {
      replaceAt(found, dest);
      pos += source.size();
      ++num_replaced;
    }
    return num_replaced;
  }
  Range split_step(value_type delimiter)
  {
    auto i = std::find(b_, e_, delimiter);
    Range result(b_, i);
    b_ = i == e_ ? e_ : std::next(i);
    return result;
  }
  Range split_step(Range delimiter)
  {
    auto i = find(delimiter);
    Range result(b_, i == std::string::npos ? size() : i);
    b_ = result.end() == e_
             ? e_
             : std::next(
                 result.end(),
                 typename std::iterator_traits<Iter>::difference_type(
                     delimiter.size()));
    return result;
  }
  template <typename TProcess, typename... Args>
  auto split_step(value_type delimiter, TProcess &&process, Args &&...args)
      -> decltype(process(std::declval<Range>(), std::forward<Args>(args)...))
  {
    return process(split_step(delimiter), std::forward<Args>(args)...);
  }
  template <typename TProcess, typename... Args>
  auto split_step(Range delimiter, TProcess &&process, Args &&...args)
      -> decltype(process(std::declval<Range>(), std::forward<Args>(args)...))
  {
    return process(split_step(delimiter), std::forward<Args>(args)...);
  }
private:
  Iter b_;
  Iter e_;
};
template <class Iter>
const typename Range<Iter>::size_type Range<Iter>::npos = std::string::npos;
template <class Iter>
void swap(Range<Iter> &lhs, Range<Iter> &rhs)
{
  lhs.swap(rhs);
}
template <class Iter>
constexpr Range<Iter> range(Iter first, Iter last)
{
  return Range<Iter>(first, last);
}
template <class Collection>
constexpr auto range(Collection &v) -> Range<decltype(v.data())>
{
  return Range<decltype(v.data())>(v.data(), v.data() + v.size());
}
template <class Collection>
constexpr auto range(Collection const &v) -> Range<decltype(v.data())>
{
  return Range<decltype(v.data())>(v.data(), v.data() + v.size());
}
template <class Collection>
constexpr auto crange(Collection const &v) -> Range<decltype(v.data())>
{
  return Range<decltype(v.data())>(v.data(), v.data() + v.size());
}
template <class T, size_t n>
constexpr Range<T *> range(T (&array)[n])
{
  return Range<T *>(array, array + n);
}
template <class T, size_t n>
constexpr Range<T const *> range(T const (&array)[n])
{
  return Range<T const *>(array, array + n);
}
template <class T, size_t n>
constexpr Range<T const *> crange(T const (&array)[n])
{
  return Range<T const *>(array, array + n);
}
template <class T, size_t n>
constexpr Range<T *> range(std::array<T, n> &array)
{
  return Range<T *>{array};
}
template <class T, size_t n>
constexpr Range<T const *> range(std::array<T, n> const &array)
{
  return Range<T const *>{array};
}
template <class T, size_t n>
constexpr Range<T const *> crange(std::array<T, n> const &array)
{
  return Range<T const *>{array};
}
typedef Range<const char *> StringPiece;
typedef Range<char *> MutableStringPiece;
typedef Range<const unsigned char *> ByteRange;
typedef Range<unsigned char *> MutableByteRange;
template <class C>
std::basic_ostream<C> &operator<<(
    std::basic_ostream<C> &os, Range<C const *> piece)
{
  using StreamSize = decltype(os.width());
  os.write(piece.start(), static_cast<StreamSize>(piece.size()));
  return os;
}
template <class C>
std::basic_ostream<C> &operator<<(std::basic_ostream<C> &os, Range<C *> piece)
{
  using StreamSize = decltype(os.width());
  os.write(piece.start(), static_cast<StreamSize>(piece.size()));
  return os;
}
template <class Iter>
inline bool operator==(const Range<Iter> &lhs, const Range<Iter> &rhs)
{
  return lhs.size() == rhs.size() && lhs.compare(rhs) == 0;
}
template <class Iter>
inline bool operator!=(const Range<Iter> &lhs, const Range<Iter> &rhs)
{
  return !(operator==(lhs, rhs));
}
template <class Iter>
inline bool operator<(const Range<Iter> &lhs, const Range<Iter> &rhs)
{
  return lhs.compare(rhs) < 0;
}
template <class Iter>
inline bool operator<=(const Range<Iter> &lhs, const Range<Iter> &rhs)
{
  return lhs.compare(rhs) <= 0;
}
template <class Iter>
inline bool operator>(const Range<Iter> &lhs, const Range<Iter> &rhs)
{
  return lhs.compare(rhs) > 0;
}
template <class Iter>
inline bool operator>=(const Range<Iter> &lhs, const Range<Iter> &rhs)
{
  return lhs.compare(rhs) >= 0;
}
namespace detail
{
template <class A, class B>
struct ComparableAsStringPiece
{
  enum
  {
    value = (std::is_convertible<A, StringPiece>::value &&
             std::is_same<B, StringPiece>::value)
            ||
            (std::is_convertible<B, StringPiece>::value &&
             std::is_same<A, StringPiece>::value)
  };
};
} // namespace detail
template <class T, class U>
std::enable_if_t<detail::ComparableAsStringPiece<T, U>::value, bool> operator==(
    const T &lhs, const U &rhs)
{
  return StringPiece(lhs) == StringPiece(rhs);
}
template <class T, class U>
std::enable_if_t<detail::ComparableAsStringPiece<T, U>::value, bool> operator!=(
    const T &lhs, const U &rhs)
{
  return StringPiece(lhs) != StringPiece(rhs);
}
template <class T, class U>
std::enable_if_t<detail::ComparableAsStringPiece<T, U>::value, bool> operator<(
    const T &lhs, const U &rhs)
{
  return StringPiece(lhs) < StringPiece(rhs);
}
template <class T, class U>
std::enable_if_t<detail::ComparableAsStringPiece<T, U>::value, bool> operator>(
    const T &lhs, const U &rhs)
{
  return StringPiece(lhs) > StringPiece(rhs);
}
template <class T, class U>
std::enable_if_t<detail::ComparableAsStringPiece<T, U>::value, bool> operator<=(
    const T &lhs, const U &rhs)
{
  return StringPiece(lhs) <= StringPiece(rhs);
}
template <class T, class U>
std::enable_if_t<detail::ComparableAsStringPiece<T, U>::value, bool> operator>=(
    const T &lhs, const U &rhs)
{
  return StringPiece(lhs) >= StringPiece(rhs);
}
template <class Iter, class Comp>
size_t qfind(const Range<Iter> &haystack, const Range<Iter> &needle, Comp eq)
{
  auto const nsize = needle.size();
  if (haystack.size() < nsize)
  {
    return std::string::npos;
  }
  if (!nsize)
  {
    return 0;
  }
  auto const nsize_1 = nsize - 1;
  auto const lastNeedle = needle[nsize_1];
  std::string::size_type skip = 0;
  auto i = haystack.begin();
  auto iEnd = haystack.end() - nsize_1;
  while (i < iEnd)
  {
    while (!eq(i[nsize_1], lastNeedle))
    {
      if (++i == iEnd)
      {
        return std::string::npos;
      }
    }
    for (size_t j = 0;;)
    {
      (static_cast<bool>(
           j < nsize
           )
           ? void(0)
           : __assert_fail(
               "j < nsize"
               ,
               "../folly/Range.h", 1294, __extension__ __PRETTY_FUNCTION__))
          ;
      if (!eq(i[j], needle[j]))
      {
        if (skip == 0)
        {
          skip = 1;
          while (skip <= nsize_1 && !eq(needle[nsize_1 - skip], lastNeedle))
          {
            ++skip;
          }
        }
        i += skip;
        break;
      }
      if (++j == nsize)
      {
        return size_t(i - haystack.begin());
      }
    }
  }
  return std::string::npos;
}
namespace detail
{
inline size_t qfind_first_byte_of(
    const StringPiece haystack, const StringPiece needles)
{
  static auto const qfind_first_byte_of_fn = folly::CpuId().sse42()
                                                 ? qfind_first_byte_of_sse42
                                                 : qfind_first_byte_of_nosse;
  return qfind_first_byte_of_fn(haystack, needles);
}
} // namespace detail
template <class Iter, class Comp>
size_t qfind_first_of(
    const Range<Iter> &haystack, const Range<Iter> &needles, Comp eq)
{
  auto ret = std::find_first_of(
      haystack.begin(), haystack.end(), needles.begin(), needles.end(), eq);
  return ret == haystack.end() ? std::string::npos : ret - haystack.begin();
}
struct AsciiCaseSensitive
{
  bool operator()(char lhs, char rhs) const
  {
    return lhs == rhs;
  }
};
struct AsciiCaseInsensitive
{
  bool operator()(char lhs, char rhs) const
  {
    char k = lhs ^ rhs;
    if (k == 0)
    {
      return true;
    }
    if (k != 32)
    {
      return false;
    }
    k = lhs | rhs;
    return (k >= 'a' && k <= 'z');
  }
};
template <class Iter>
size_t qfind(
    const Range<Iter> &haystack,
    const typename Range<Iter>::value_type &needle)
{
  auto pos = std::find(haystack.begin(), haystack.end(), needle);
  return pos == haystack.end() ? std::string::npos : pos - haystack.data();
}
template <class Iter>
size_t rfind(
    const Range<Iter> &haystack,
    const typename Range<Iter>::value_type &needle)
{
  for (auto i = haystack.size(); i-- > 0;)
  {
    if (haystack[i] == needle)
    {
      return i;
    }
  }
  return std::string::npos;
}
template <>
inline size_t qfind(const Range<const char *> &haystack, const char &needle)
{
  if (haystack.empty())
  {
    return std::string::npos;
  }
  auto pos = static_cast<const char *>(
      ::memchr(haystack.data(), needle, haystack.size()));
  return pos == nullptr ? std::string::npos : pos - haystack.data();
}
template <>
inline size_t rfind(const Range<const char *> &haystack, const char &needle)
{
  if (haystack.empty())
  {
    return std::string::npos;
  }
  auto pos = static_cast<const char *>(
      memrchr(haystack.data(), needle, haystack.size()));
  return pos == nullptr ? std::string::npos : pos - haystack.data();
}
template <>
inline size_t qfind(
    const Range<const unsigned char *> &haystack, const unsigned char &needle)
{
  if (haystack.empty())
  {
    return std::string::npos;
  }
  auto pos = static_cast<const unsigned char *>(
      ::memchr(haystack.data(), needle, haystack.size()));
  return pos == nullptr ? std::string::npos : pos - haystack.data();
}
template <>
inline size_t rfind(
    const Range<const unsigned char *> &haystack, const unsigned char &needle)
{
  if (haystack.empty())
  {
    return std::string::npos;
  }
  auto pos = static_cast<const unsigned char *>(
      memrchr(haystack.data(), needle, haystack.size()));
  return pos == nullptr ? std::string::npos : pos - haystack.data();
}
template <class Iter>
size_t qfind_first_of(const Range<Iter> &haystack, const Range<Iter> &needles)
{
  return qfind_first_of(haystack, needles, AsciiCaseSensitive());
}
template <>
inline size_t qfind_first_of(
    const Range<const char *> &haystack, const Range<const char *> &needles)
{
  return detail::qfind_first_byte_of(haystack, needles);
}
template <>
inline size_t qfind_first_of(
    const Range<const unsigned char *> &haystack,
    const Range<const unsigned char *> &needles)
{
  return detail::qfind_first_byte_of(
      StringPiece(haystack), StringPiece(needles));
}
template <class Key, class Enable>
struct hasher;
template <class T>
struct hasher<
    folly::Range<T *>,
    std::enable_if_t<std::is_integral<T>::value, void>>
{
  using folly_is_avalanching = std::true_type;
  size_t operator()(folly::Range<T *> r) const
  {
    return static_cast<size_t>(
        hash::SpookyHashV2::Hash64(r.begin(), r.size() * sizeof(T), 0));
  }
};
inline namespace literals
{
inline namespace string_piece_literals
{
constexpr Range<char const *> operator"" _sp(
    char const *str, size_t len) noexcept
{
  return Range<char const *>(str, len);
}
constexpr Range<char16_t const *> operator"" _sp(
    char16_t const *str, size_t len) noexcept
{
  return Range<char16_t const *>(str, len);
}
constexpr Range<char32_t const *> operator"" _sp(
    char32_t const *str, size_t len) noexcept
{
  return Range<char32_t const *>(str, len);
}
constexpr Range<wchar_t const *> operator"" _sp(
    wchar_t const *str, size_t len) noexcept
{
  return Range<wchar_t const *>(str, len);
}
} // namespace string_piece_literals
} // namespace literals
} // namespace folly
namespace folly
{
template <class T1>
struct IsRelocatable<folly::Range<T1>> : std::true_type
{
};
} // namespace folly
namespace ranges
{
template <class T>
extern const bool enable_view;
}
namespace ranges
{
template <class Iter>
inline constexpr bool enable_view<::folly::Range<Iter>> = true;
}
namespace folly
{
template <typename T>
constexpr typename std::decay<T>::type copy(T &&value) noexcept(
    noexcept(typename std::decay<T>::type(std::forward<T>(value))))
{
  return std::forward<T>(value);
}
using std::as_const;
template <typename Src, typename Dst>
constexpr like_t<Src, Dst> &&forward_like(Dst &&dst) noexcept
{
  return std::forward<like_t<Src, Dst>>(static_cast<Dst &&>(dst));
}
struct in_place_tag
{
};
template <class>
struct in_place_type_tag
{
};
template <std::size_t>
struct in_place_index_tag
{
};
using in_place_t = in_place_tag (&)(in_place_tag);
template <class T>
using in_place_type_t = in_place_type_tag<T> (&)(in_place_type_tag<T>);
template <std::size_t I>
using in_place_index_t = in_place_index_tag<I> (&)(in_place_index_tag<I>);
inline in_place_tag in_place(in_place_tag = {})
{
  return {};
}
template <class T>
inline in_place_type_tag<T> in_place_type(in_place_type_tag<T> = {})
{
  return {};
}
template <std::size_t I>
inline in_place_index_tag<I> in_place_index(in_place_index_tag<I> = {})
{
  return {};
}
struct initlist_construct_t
{
};
constexpr initlist_construct_t initlist_construct{};
struct sorted_unique_t
{
};
constexpr sorted_unique_t sorted_unique;
struct sorted_equivalent_t
{
};
constexpr sorted_equivalent_t sorted_equivalent;
template <typename T>
struct transparent : T
{
  using is_transparent = void;
  using T::T;
};
struct identity_fn
{
  template <class T>
  constexpr T &&operator()(T &&x) const noexcept
  {
    return static_cast<T &&>(x);
  }
};
using Identity = identity_fn;
inline constexpr identity_fn identity;
namespace moveonly_
{
class MoveOnly
{
protected:
  constexpr MoveOnly() = default;
  ~MoveOnly() = default;
  MoveOnly(MoveOnly &&) = default;
  MoveOnly &operator=(MoveOnly &&) = default;
  MoveOnly(const MoveOnly &) = delete;
  MoveOnly &operator=(const MoveOnly &) = delete;
};
} // namespace moveonly_
using MoveOnly = moveonly_::MoveOnly;
struct to_signed_fn
{
  template <typename..., typename T>
  constexpr auto operator()(T const &t) const noexcept ->
      typename std::make_signed<T>::type
  {
    using S = typename std::make_signed<T>::type;
    constexpr auto m = static_cast<T>(std::numeric_limits<S>::max());
    return m < t ? -static_cast<S>(~t) + S{-1} : static_cast<S>(t);
  }
};
inline constexpr to_signed_fn to_signed;
struct to_unsigned_fn
{
  template <typename..., typename T>
  constexpr auto operator()(T const &t) const noexcept ->
      typename std::make_unsigned<T>::type
  {
    using U = typename std::make_unsigned<T>::type;
    return static_cast<U>(t);
  }
};
inline constexpr to_unsigned_fn to_unsigned;
template <typename Src>
class to_narrow_convertible
{
public:
  static_assert(std::is_integral<Src>::value, "not an integer");
  explicit constexpr to_narrow_convertible(Src const &value) noexcept
      : value_(value)
  {
  }
  explicit to_narrow_convertible(to_narrow_convertible const &) = default;
  explicit to_narrow_convertible(to_narrow_convertible &&) = default;
  to_narrow_convertible &operator=(to_narrow_convertible const &) = default;
  to_narrow_convertible &operator=(to_narrow_convertible &&) = default;
  template <
      typename Dst,
      std::enable_if_t<
          std::is_integral<Dst>::value &&
              std::is_signed<Dst>::value == std::is_signed<Src>::value,
          int> = 0>
  constexpr operator Dst() const noexcept
  {
    return value_;
  }
private:
  Src value_;
};
struct to_narrow_fn
{
  template <typename..., typename Src>
  constexpr auto operator()(Src const &src) const noexcept
      -> to_narrow_convertible<Src>
  {
    return to_narrow_convertible<Src>{src};
  }
};
inline constexpr to_narrow_fn to_narrow;
struct to_underlying_fn
{
  template <typename..., class E>
  constexpr std::underlying_type_t<E> operator()(E e) const noexcept
  {
    static_assert(std::is_enum<E>::value, "not an enum type");
    return static_cast<std::underlying_type_t<E>>(e);
  }
};
inline constexpr to_underlying_fn to_underlying;
namespace detail
{
struct thunk
{
  template <typename T>
  static void *make()
  {
    return new T();
  }
  template <typename T>
  static void ruin(void *ptr) noexcept
  {
    delete static_cast<T *>(ptr);
  }
  template <typename T>
  static void ctor(void *ptr)
  {
    ::new (ptr) T();
  }
  template <typename T>
  static void dtor(void *ptr) noexcept
  {
    static_cast<T *>(ptr)->~T();
  }
};
} // namespace detail
} // namespace folly
namespace folly
{
enum class ordering : int
{
  lt = -1,
  eq = 0,
  gt = 1
};
template <typename T>
constexpr ordering to_ordering(T c)
{
  return ordering(int(c < T(0)) * -1 + int(c > T(0)));
}
namespace detail
{
template <typename C, ordering o, bool ne>
struct cmp_pred : private C
{
  using C::C;
  template <typename A, typename B>
  constexpr bool operator()(A &&a, B &&b) const
  {
    return ne ^ (C::operator()(static_cast<A &&>(a), static_cast<B &&>(b)) == o);
  }
};
} // namespace detail
template <typename C>
struct compare_equal_to : detail::cmp_pred<C, ordering::eq, 0>
{
  using detail::cmp_pred<C, ordering::eq, 0>::cmp_pred;
};
template <typename C>
struct compare_not_equal_to : detail::cmp_pred<C, ordering::eq, 1>
{
  using detail::cmp_pred<C, ordering::eq, 1>::cmp_pred;
};
template <typename C>
struct compare_less : detail::cmp_pred<C, ordering::lt, 0>
{
  using detail::cmp_pred<C, ordering::lt, 0>::cmp_pred;
};
template <typename C>
struct compare_less_equal : detail::cmp_pred<C, ordering::gt, 1>
{
  using detail::cmp_pred<C, ordering::gt, 1>::cmp_pred;
};
template <typename C>
struct compare_greater : detail::cmp_pred<C, ordering::gt, 0>
{
  using detail::cmp_pred<C, ordering::gt, 0>::cmp_pred;
};
template <typename C>
struct compare_greater_equal : detail::cmp_pred<C, ordering::lt, 1>
{
  using detail::cmp_pred<C, ordering::lt, 1>::cmp_pred;
};
} // namespace folly
namespace folly
{
template <class Char, std::size_t N>
class BasicFixedString;
template <std::size_t N>
using FixedString = BasicFixedString<char, N>;
namespace detail
{
namespace fixedstring
{
template <class = void>
struct FixedStringBase_
{
  static constexpr std::size_t npos = static_cast<std::size_t>(-1);
};
template <class Void>
constexpr std::size_t FixedStringBase_<Void>::npos;
using FixedStringBase = FixedStringBase_<>;
[[noreturn]] inline void assertOutOfBounds()
{
  (static_cast<bool>(
       !"Array index out of bounds in BasicFixedString"
       )
       ? void(0)
       : __assert_fail(
           "!\"Array index out of bounds in BasicFixedString\""
           ,
           "../folly/FixedString.h", 67, __extension__ __PRETTY_FUNCTION__))
      ;
  throw_exception<std::out_of_range>(
      "Array index out of bounds in BasicFixedString");
}
constexpr std::size_t checkOverflow(std::size_t i, std::size_t max)
{
  return i <= max ? i : (void(assertOutOfBounds()), max);
}
constexpr std::size_t checkOverflowOrNpos(std::size_t i, std::size_t max)
{
  return i == FixedStringBase::npos
             ? max
             : (i <= max ? i : (void(assertOutOfBounds()), max));
}
constexpr std::size_t checkOverflowIfDebug(std::size_t i, std::size_t size)
{
  return kIsDebug ? checkOverflow(i, size) : i;
}
[[noreturn]] inline void assertNotNullTerminated() noexcept
{
  (static_cast<bool>(
       !"Non-null terminated string used to initialize a BasicFixedString"
       )
       ? void(0)
       : __assert_fail(
           "!\"Non-null terminated string used to initialize a BasicFixedString\""
           ,
           "../folly/FixedString.h", 88, __extension__ __PRETTY_FUNCTION__))
      ;
  std::terminate();
}
template <class Char, std::size_t N>
constexpr const Char (&checkNullTerminated(const Char (&a)[N]) noexcept)[N]
{
  return a[N - 1u] == Char(0)
                 && (!kIsDebug || N - 1u == folly::constexpr_strlen(a))
             ? decltype(a)(a)
             : (assertNotNullTerminated(), decltype(a)(a));
}
template <class Left, class Right>
constexpr ordering compare_(
    const Left &left,
    std::size_t left_pos,
    std::size_t left_size,
    const Right &right,
    std::size_t right_pos,
    std::size_t right_size) noexcept
{
  return left_pos == left_size
             ? (right_pos == right_size ? ordering::eq : ordering::lt)
             : (right_pos == right_size ? ordering::gt
                                        : (left[left_pos] < right[right_pos]
                                               ? ordering::lt
                                               : (left[left_pos] > right[right_pos]
                                                      ? ordering::gt
                                                      : fixedstring::compare_(
                                                          left,
                                                          left_pos + 1u,
                                                          left_size,
                                                          right,
                                                          right_pos + 1u,
                                                          right_size))));
}
template <class Left, class Right>
constexpr bool equal_(
    const Left &left,
    std::size_t left_size,
    const Right &right,
    std::size_t right_size) noexcept
{
  return left_size == right_size &&
         ordering::eq == compare_(left, 0u, left_size, right, 0u, right_size);
}
template <class Char, class Left, class Right>
constexpr Char char_at_(
    const Left &left,
    std::size_t left_count,
    const Right &right,
    std::size_t right_count,
    std::size_t i) noexcept
{
  return i < left_count ? left[i]
         : i < (left_count + right_count) ? right[i - left_count]
                                          : Char(0);
}
template <class Char, class Left, class Right>
constexpr Char char_at_(
    const Left &left,
    std::size_t left_size,
    std::size_t left_pos,
    std::size_t left_count,
    const Right &right,
    std::size_t right_pos,
    std::size_t right_count,
    std::size_t i) noexcept
{
  return i < left_pos
             ? left[i]
             : (i < right_count + left_pos ? right[i - left_pos + right_pos]
                                           : (i < left_size - left_count + right_count
                                                  ? left[i - right_count + left_count]
                                                  : Char(0)));
}
template <class Left, class Right>
constexpr bool find_at_(
    const Left &left,
    const Right &right,
    std::size_t pos,
    std::size_t count) noexcept
{
  return 0u == count ||
         (left[pos + count - 1u] == right[count - 1u] &&
          find_at_(left, right, pos, count - 1u));
}
template <class Char, class Right>
constexpr bool find_one_of_at_(
    Char ch, const Right &right, std::size_t pos) noexcept
{
  return 0u != pos &&
         (ch == right[pos - 1u] || find_one_of_at_(ch, right, pos - 1u));
}
template <class Left, class Right>
constexpr std::size_t find_(
    const Left &left,
    std::size_t left_size,
    const Right &right,
    std::size_t pos,
    std::size_t count) noexcept
{
  return find_at_(left, right, pos, count) ? pos
         : left_size <= pos + count
             ? FixedStringBase::npos
             : find_(left, left_size, right, pos + 1u, count);
}
template <class Left, class Right>
constexpr std::size_t rfind_(
    const Left &left,
    const Right &right,
    std::size_t pos,
    std::size_t count) noexcept
{
  return find_at_(left, right, pos, count) ? pos
         : 0u == pos ? FixedStringBase::npos
                     : rfind_(left, right, pos - 1u, count);
}
template <class Left, class Right>
constexpr std::size_t find_first_of_(
    const Left &left,
    std::size_t left_size,
    const Right &right,
    std::size_t pos,
    std::size_t count) noexcept
{
  return find_one_of_at_(left[pos], right, count) ? pos
         : left_size <= pos + 1u
             ? FixedStringBase::npos
             : find_first_of_(left, left_size, right, pos + 1u, count);
}
template <class Left, class Right>
constexpr std::size_t find_first_not_of_(
    const Left &left,
    std::size_t left_size,
    const Right &right,
    std::size_t pos,
    std::size_t count) noexcept
{
  return !find_one_of_at_(left[pos], right, count) ? pos
         : left_size <= pos + 1u
             ? FixedStringBase::npos
             : find_first_not_of_(left, left_size, right, pos + 1u, count);
}
template <class Left, class Right>
constexpr std::size_t find_last_of_(
    const Left &left,
    const Right &right,
    std::size_t pos,
    std::size_t count) noexcept
{
  return find_one_of_at_(left[pos], right, count) ? pos
         : 0u == pos ? FixedStringBase::npos
                     : find_last_of_(left, right, pos - 1u, count);
}
template <class Left, class Right>
constexpr std::size_t find_last_not_of_(
    const Left &left,
    const Right &right,
    std::size_t pos,
    std::size_t count) noexcept
{
  return !find_one_of_at_(left[pos], right, count) ? pos
         : 0u == pos ? FixedStringBase::npos
                     : find_last_not_of_(left, right, pos - 1u, count);
}
struct Helper
{
  template <class Char, class Left, class Right, std::size_t... Is>
  static constexpr BasicFixedString<Char, sizeof...(Is)> concat_(
      const Left &left,
      std::size_t left_count,
      const Right &right,
      std::size_t right_count,
      std::index_sequence<Is...> is) noexcept
  {
    return {left, left_count, right, right_count, is};
  }
  template <class Char, class Left, class Right, std::size_t... Is>
  static constexpr BasicFixedString<Char, sizeof...(Is)> replace_(
      const Left &left,
      std::size_t left_size,
      std::size_t left_pos,
      std::size_t left_count,
      const Right &right,
      std::size_t right_pos,
      std::size_t right_count,
      std::index_sequence<Is...> is) noexcept
  {
    return {
        left,
        left_size,
        left_pos,
        left_count,
        right,
        right_pos,
        right_count,
        is};
  }
  template <class Char, std::size_t N>
  static constexpr const Char (
      &data_(const BasicFixedString<Char, N> &that) noexcept)[N + 1u]
  {
    return that.data_;
  }
};
template <class T>
constexpr void constexpr_swap(T &a, T &b) noexcept(
    noexcept(a = T(std::move(a))))
{
  T tmp((std::move(a)));
  a = std::move(b);
  b = std::move(tmp);
}
template <class T>
struct ReverseIterator
{
private:
  T *p_ = nullptr;
  struct dummy_
  {
    T *p_ = nullptr;
  };
  using other = typename std::conditional<
      std::is_const<T>::value,
      ReverseIterator<typename std::remove_const<T>::type>,
      dummy_>::type;
public:
  using value_type = typename std::remove_const<T>::type;
  using reference = T &;
  using pointer = T *;
  using difference_type = std::ptrdiff_t;
  using iterator_category = std::random_access_iterator_tag;
  constexpr ReverseIterator() = default;
  constexpr ReverseIterator(const ReverseIterator &) = default;
  constexpr ReverseIterator &operator=(const ReverseIterator &) = default;
  constexpr explicit ReverseIterator(T *p) noexcept
      : p_(p)
  {
  }
  constexpr ReverseIterator(const other &that) noexcept
      : p_(that.p_)
  {
  }
  friend constexpr bool operator==(
      ReverseIterator a, ReverseIterator b) noexcept
  {
    return a.p_ == b.p_;
  }
  friend constexpr bool operator!=(
      ReverseIterator a, ReverseIterator b) noexcept
  {
    return !(a == b);
  }
  constexpr reference operator*() const
  {
    return *(p_ - 1);
  }
  constexpr ReverseIterator &operator++() noexcept
  {
    --p_;
    return *this;
  }
  constexpr ReverseIterator operator++(int) noexcept
  {
    auto tmp(*this);
    --p_;
    return tmp;
  }
  constexpr ReverseIterator &operator--() noexcept
  {
    ++p_;
    return *this;
  }
  constexpr ReverseIterator operator--(int) noexcept
  {
    auto tmp(*this);
    ++p_;
    return tmp;
  }
  constexpr ReverseIterator &operator+=(std::ptrdiff_t i) noexcept
  {
    p_ -= i;
    return *this;
  }
  friend constexpr ReverseIterator operator+(
      std::ptrdiff_t i, ReverseIterator that) noexcept
  {
    return ReverseIterator{that.p_ - i};
  }
  friend constexpr ReverseIterator operator+(
      ReverseIterator that, std::ptrdiff_t i) noexcept
  {
    return ReverseIterator{that.p_ - i};
  }
  constexpr ReverseIterator &operator-=(std::ptrdiff_t i) noexcept
  {
    p_ += i;
    return *this;
  }
  friend constexpr ReverseIterator operator-(
      ReverseIterator that, std::ptrdiff_t i) noexcept
  {
    return ReverseIterator{that.p_ + i};
  }
  friend constexpr std::ptrdiff_t operator-(
      ReverseIterator a, ReverseIterator b) noexcept
  {
    return b.p_ - a.p_;
  }
  constexpr reference operator[](std::ptrdiff_t i) const noexcept
  {
    return *(*this + i);
  }
};
} // namespace fixedstring
} // namespace detail
std::uint32_t hsieh_hash32_buf(const void *buf, std::size_t len);
template <class Char, std::size_t N>
class BasicFixedString : private detail::fixedstring::FixedStringBase
{
private:
  template <class, std::size_t>
  friend class BasicFixedString;
  friend struct detail::fixedstring::Helper;
  Char data_[N + 1u];
  std::size_t size_;
  using Indices = std::make_index_sequence<N>;
  template <class That, std::size_t... Is>
  constexpr BasicFixedString(
      const That &that,
      std::size_t size,
      std::index_sequence<Is...>,
      std::size_t pos = 0,
      std::size_t count = npos) noexcept
      : data_{(Is < (size - pos) && Is < count ? that[Is + pos] : Char(0))..., Char(0)},
        size_{folly::constexpr_min(size - pos, count)}
  {
  }
  template <std::size_t... Is>
  constexpr BasicFixedString(
      std::size_t count, Char ch, std::index_sequence<Is...>) noexcept
      : data_{((Is < count) ? ch : Char(0))..., Char(0)}, size_{count}
  {
  }
  template <class Left, class Right, std::size_t... Is>
  constexpr BasicFixedString(
      const Left &left,
      std::size_t left_size,
      const Right &right,
      std::size_t right_size,
      std::index_sequence<Is...>) noexcept
      : data_{detail::fixedstring::char_at_<Char>(left, left_size, right, right_size, Is)..., Char(0)},
        size_{left_size + right_size}
  {
  }
  template <class Left, class Right, std::size_t... Is>
  constexpr BasicFixedString(
      const Left &left,
      std::size_t left_size,
      std::size_t left_pos,
      std::size_t left_count,
      const Right &right,
      std::size_t right_pos,
      std::size_t right_count,
      std::index_sequence<Is...>) noexcept
      : data_{detail::fixedstring::char_at_<Char>(left, left_size, left_pos, left_count, right, right_pos, right_count, Is)..., Char(0)},
        size_{left_size - left_count + right_count}
  {
  }
public:
  using size_type = std::size_t;
  using difference_type = std::ptrdiff_t;
  using reference = Char &;
  using const_reference = const Char &;
  using pointer = Char *;
  using const_pointer = const Char *;
  using iterator = Char *;
  using const_iterator = const Char *;
  using reverse_iterator = detail::fixedstring::ReverseIterator<Char>;
  using const_reverse_iterator =
      detail::fixedstring::ReverseIterator<const Char>;
  using detail::fixedstring::FixedStringBase::npos;
  constexpr BasicFixedString()
      : data_{}, size_{}
  {
  }
  constexpr BasicFixedString(const BasicFixedString &) = default;
  template <std::size_t M>
  constexpr BasicFixedString(
      const BasicFixedString<Char, M> &that) noexcept(M <= N)
      : BasicFixedString{that, 0u, that.size_}
  {
  }
  template <std::size_t M>
  constexpr BasicFixedString(
      const BasicFixedString<Char, M> &that,
      std::size_t pos) noexcept(false)
      = delete;
  template <std::size_t M>
  constexpr BasicFixedString(
      const BasicFixedString<Char, M> &that,
      std::size_t pos,
      std::size_t count) noexcept(false)
      : BasicFixedString{
          that.data_,
          that.size_,
          std::make_index_sequence<(M < N ? M : N)>{},
          pos,
          detail::fixedstring::checkOverflow(
              detail::fixedstring::checkOverflowOrNpos(
                  count,
                  that.size_ -
                      detail::fixedstring::checkOverflow(pos, that.size_)),
              N)}
  {
  }
  template <std::size_t M, class = typename std::enable_if<(M - 1u <= N)>::type>
  constexpr BasicFixedString(const Char (&that)[M]) noexcept
      : BasicFixedString{
          detail::fixedstring::checkNullTerminated(that),
          M - 1u,
          std::make_index_sequence<M - 1u>{}}
  {
  }
  constexpr BasicFixedString(const Char *that, std::size_t count) noexcept(
      false)
      : BasicFixedString{
          that, detail::fixedstring::checkOverflow(count, N), Indices{}}
  {
  }
  constexpr BasicFixedString(std::size_t count, Char ch) noexcept(false)
      : BasicFixedString{
          detail::fixedstring::checkOverflow(count, N), ch, Indices{}}
  {
  }
  constexpr BasicFixedString(std::initializer_list<Char> il) noexcept(false)
      : BasicFixedString{il.begin(), il.size()}
  {
  }
  constexpr BasicFixedString &operator=(const BasicFixedString &) noexcept =
      default;
  template <std::size_t M>
  constexpr BasicFixedString &operator=(
      const BasicFixedString<Char, M> &that) noexcept(M <= N)
  {
    detail::fixedstring::checkOverflow(that.size_, N);
    size_ = that.copy(data_, that.size_);
    data_[size_] = Char(0);
    return *this;
  }
  template <std::size_t M, class = typename std::enable_if<(M - 1u <= N)>::type>
  constexpr BasicFixedString &operator=(const Char (&that)[M]) noexcept
  {
    return assign(detail::fixedstring::checkNullTerminated(that), M - 1u);
  }
  constexpr BasicFixedString &operator=(
      std::initializer_list<Char> il) noexcept(false)
  {
    detail::fixedstring::checkOverflow(il.size(), N);
    for (std::size_t i = 0u; i < il.size(); ++i)
    {
      data_[i] = il.begin()[i];
    }
    size_ = il.size();
    data_[size_] = Char(0);
    return *this;
  }
  constexpr Range<Char *> toRange() noexcept
  {
    return {begin(), end()};
  }
  constexpr Range<const Char *> toRange() const noexcept
  {
    return {begin(), end()};
  }
  operator std::basic_string<Char>() const noexcept(false)
  {
    return std::basic_string<Char>{begin(), end()};
  }
  std::basic_string<Char> toStdString() const noexcept(false)
  {
    return std::basic_string<Char>{begin(), end()};
  }
  constexpr BasicFixedString &assign(std::size_t count, Char ch) noexcept(
      false)
  {
    detail::fixedstring::checkOverflow(count, N);
    for (std::size_t i = 0u; i < count; ++i)
    {
      data_[i] = ch;
    }
    size_ = count;
    data_[size_] = Char(0);
    return *this;
  }
  template <std::size_t M>
  constexpr BasicFixedString &assign(
      const BasicFixedString<Char, M> &that) noexcept(M <= N)
  {
    return *this = that;
  }
  template <std::size_t M>
  constexpr BasicFixedString &assign(
      const BasicFixedString<Char, M> &that,
      std::size_t pos) noexcept(false)
      = delete;
  template <std::size_t M>
  constexpr BasicFixedString &assign(
      const BasicFixedString<Char, M> &that,
      std::size_t pos,
      std::size_t count) noexcept(false)
  {
    detail::fixedstring::checkOverflow(pos, that.size_);
    return assign(
        that.data_ + pos,
        detail::fixedstring::checkOverflowOrNpos(count, that.size_ - pos));
  }
  template <std::size_t M, class = typename std::enable_if<(M - 1u <= N)>::type>
  constexpr BasicFixedString &assign(const Char (&that)[M]) noexcept
  {
    return assign(detail::fixedstring::checkNullTerminated(that), M - 1u);
  }
  constexpr BasicFixedString &assign(
      const Char *that, std::size_t count) noexcept(false)
  {
    detail::fixedstring::checkOverflow(count, N);
    for (std::size_t i = 0u; i < count; ++i)
    {
      data_[i] = that[i];
    }
    size_ = count;
    data_[size_] = Char(0);
    return *this;
  }
  constexpr void swap(BasicFixedString &that) noexcept
  {
    for (std::size_t i = 0u; i <= folly::constexpr_max(size_, that.size_);
         ++i)
    {
      detail::fixedstring::constexpr_swap(data_[i], that.data_[i]);
    }
    detail::fixedstring::constexpr_swap(size_, that.size_);
  }
  constexpr Char *data() noexcept
  {
    return data_;
  }
  constexpr const Char *data() const noexcept
  {
    return data_;
  }
  constexpr const Char *c_str() const noexcept
  {
    return data_;
  }
  constexpr Char *begin() noexcept
  {
    return data_;
  }
  constexpr const Char *begin() const noexcept
  {
    return data_;
  }
  constexpr const Char *cbegin() const noexcept
  {
    return begin();
  }
  constexpr Char *end() noexcept
  {
    return data_ + size_;
  }
  constexpr const Char *end() const noexcept
  {
    return data_ + size_;
  }
  constexpr const Char *cend() const noexcept
  {
    return end();
  }
  constexpr reverse_iterator rbegin() noexcept
  {
    return reverse_iterator{data_ + size_};
  }
  constexpr const_reverse_iterator rbegin() const noexcept
  {
    return const_reverse_iterator{data_ + size_};
  }
  constexpr const_reverse_iterator crbegin() const noexcept
  {
    return rbegin();
  }
  constexpr reverse_iterator rend() noexcept
  {
    return reverse_iterator{data_};
  }
  constexpr const_reverse_iterator rend() const noexcept
  {
    return const_reverse_iterator{data_};
  }
  constexpr const_reverse_iterator crend() const noexcept
  {
    return rend();
  }
  constexpr std::size_t size() const noexcept
  {
    return size_;
  }
  constexpr std::size_t length() const noexcept
  {
    return size_;
  }
  constexpr bool empty() const noexcept
  {
    return 0u == size_;
  }
  static constexpr std::size_t capacity() noexcept
  {
    return N;
  }
  static constexpr std::size_t max_size() noexcept
  {
    return N;
  }
  std::uint32_t hash() const noexcept
  {
    return folly::hsieh_hash32_buf(data_, size_);
  }
  constexpr Char &at(std::size_t i) noexcept(false)
  {
    return i <= size_ ? data_[i]
                      : (throw_exception<std::out_of_range>(
                             "Out of range in BasicFixedString::at"),
                         data_[size_]);
  }
  constexpr const Char &at(std::size_t i) const noexcept(false)
  {
    return i <= size_ ? data_[i]
                      : (throw_exception<std::out_of_range>(
                             "Out of range in BasicFixedString::at"),
                         data_[size_]);
  }
  constexpr Char &operator[](std::size_t i) noexcept
  {
    return data_[detail::fixedstring::checkOverflowIfDebug(i, size_)];
  }
  constexpr const Char &operator[](std::size_t i) const noexcept
  {
    return data_[detail::fixedstring::checkOverflowIfDebug(i, size_)];
  }
  constexpr Char &front() noexcept
  {
    return (*this)[0u];
  }
  constexpr const Char &front() const noexcept
  {
    return (*this)[0u];
  }
  constexpr Char &back() noexcept
  {
    return data_[size_ - detail::fixedstring::checkOverflowIfDebug(1u, size_)];
  }
  constexpr const Char &back() const noexcept
  {
    return data_[size_ - detail::fixedstring::checkOverflowIfDebug(1u, size_)];
  }
  constexpr void clear() noexcept
  {
    data_[0u] = Char(0);
    size_ = 0u;
  }
  constexpr void push_back(Char ch) noexcept(false)
  {
    detail::fixedstring::checkOverflow(1u, N - size_);
    data_[size_] = ch;
    data_[++size_] = Char(0);
  }
  constexpr BasicFixedString<Char, N + 1u> cpush_back(Char ch) const noexcept
  {
    return cappend(ch);
  }
  constexpr void pop_back() noexcept(false)
  {
    detail::fixedstring::checkOverflow(1u, size_);
    --size_;
    data_[size_] = Char(0);
  }
  constexpr BasicFixedString<Char, N - 1u> cpop_back() const noexcept(false)
  {
    return {*this, 0u, size_ - detail::fixedstring::checkOverflow(1u, size_)};
  }
  constexpr BasicFixedString &append(std::size_t count, Char ch) noexcept(
      false)
  {
    detail::fixedstring::checkOverflow(count, N - size_);
    for (std::size_t i = 0u; i < count; ++i)
    {
      data_[size_ + i] = ch;
    }
    size_ += count;
    data_[size_] = Char(0);
    return *this;
  }
  template <std::size_t M>
  constexpr BasicFixedString &append(
      const BasicFixedString<Char, M> &that) noexcept(false)
  {
    return append(that, 0u, that.size_);
  }
  template <std::size_t M>
  constexpr BasicFixedString &append(
      const BasicFixedString<Char, M> &that,
      std::size_t pos) noexcept(false)
      = delete;
  template <std::size_t M>
  constexpr BasicFixedString &append(
      const BasicFixedString<Char, M> &that,
      std::size_t pos,
      std::size_t count) noexcept(false)
  {
    detail::fixedstring::checkOverflow(pos, that.size_);
    count = detail::fixedstring::checkOverflowOrNpos(count, that.size_ - pos);
    detail::fixedstring::checkOverflow(count, N - size_);
    for (std::size_t i = 0u; i < count; ++i)
    {
      data_[size_ + i] = that.data_[pos + i];
    }
    size_ += count;
    data_[size_] = Char(0);
    return *this;
  }
  constexpr BasicFixedString &append(const Char *that) noexcept(false)
  {
    return append(that, folly::constexpr_strlen(that));
  }
  constexpr BasicFixedString &append(
      const Char *that, std::size_t count) noexcept(false)
  {
    detail::fixedstring::checkOverflow(count, N - size_);
    for (std::size_t i = 0u; i < count; ++i)
    {
      data_[size_ + i] = that[i];
    }
    size_ += count;
    data_[size_] = Char(0);
    return *this;
  }
  constexpr BasicFixedString<Char, N + 1u> cappend(Char ch) const noexcept
  {
    return *this + ch;
  }
  template <std::size_t M>
  constexpr BasicFixedString<Char, N + M> cappend(
      const BasicFixedString<Char, M> &that) const noexcept
  {
    return *this + that;
  }
  template <std::size_t M>
  constexpr BasicFixedString<Char, N + M> cappend(
      const BasicFixedString<Char, M> &that, std::size_t pos) const
      noexcept(false)
      = delete;
  template <std::size_t M>
  constexpr BasicFixedString<Char, N + M> cappend(
      const BasicFixedString<Char, M> &that,
      std::size_t pos,
      std::size_t count) const noexcept(false)
  {
    return creplace(size_, 0u, that, pos, count);
  }
  template <std::size_t M>
  constexpr BasicFixedString<Char, N + M - 1u> cappend(
      const Char (&that)[M]) const noexcept
  {
    return creplace(size_, 0u, that);
  }
  template <std::size_t M>
  constexpr BasicFixedString<Char, N + M - 1u> cappend(
      const Char (&that)[M], std::size_t pos) const noexcept(false)
      = delete;
  template <std::size_t M>
  constexpr BasicFixedString<Char, N + M - 1u> cappend(
      const Char (&that)[M], std::size_t pos, std::size_t count) const
      noexcept(false)
  {
    return creplace(size_, 0u, that, pos, count);
  }
  constexpr BasicFixedString &operator+=(const Char *that) noexcept(false)
  {
    return append(that);
  }
  template <std::size_t M>
  constexpr BasicFixedString &operator+=(
      const BasicFixedString<Char, M> &that) noexcept(false)
  {
    return append(that, 0u, that.size_);
  }
  constexpr BasicFixedString &operator+=(Char ch) noexcept(false)
  {
    push_back(ch);
    return *this;
  }
  constexpr BasicFixedString &operator+=(
      std::initializer_list<Char> il) noexcept(false)
  {
    return append(il.begin(), il.size());
  }
  constexpr BasicFixedString &erase() noexcept
  {
    clear();
    return *this;
  }
  constexpr BasicFixedString &erase(
      std::size_t pos, std::size_t count = npos) noexcept(false)
  {
    using A = const Char[1];
    constexpr A a{Char(0)};
    return replace(
        pos,
        detail::fixedstring::checkOverflowOrNpos(
            count, size_ - detail::fixedstring::checkOverflow(pos, size_)),
        a,
        0u);
  }
  constexpr Char *erase(const Char *first) noexcept(false)
  {
    erase(first - data_, 1u);
    return data_ + (first - data_);
  }
  constexpr Char *erase(const Char *first, const Char *last) noexcept(false)
  {
    erase(first - data_, last - first);
    return data_ + (first - data_);
  }
  constexpr BasicFixedString<Char, 0u> cerase() const noexcept
  {
    return {};
  }
  constexpr BasicFixedString cerase(
      std::size_t pos, std::size_t count = npos) const noexcept(false)
  {
    using A = const Char[1];
    return creplace(
        pos,
        detail::fixedstring::checkOverflowOrNpos(
            count, size_ - detail::fixedstring::checkOverflow(pos, size_)),
        A{Char(0)});
  }
  template <std::size_t M>
  constexpr int compare(const BasicFixedString<Char, M> &that) const noexcept
  {
    return compare(0u, size_, that, 0u, that.size_);
  }
  template <std::size_t M>
  constexpr int compare(
      std::size_t this_pos,
      std::size_t this_count,
      const BasicFixedString<Char, M> &that) const noexcept(false)
  {
    return compare(this_pos, this_count, that, 0u, that.size_);
  }
  template <std::size_t M>
  constexpr int compare(
      std::size_t this_pos,
      std::size_t this_count,
      const BasicFixedString<Char, M> &that,
      std::size_t that_pos,
      std::size_t that_count) const noexcept(false)
  {
    return static_cast<int>(detail::fixedstring::compare_(
        data_,
        detail::fixedstring::checkOverflow(this_pos, size_),
        detail::fixedstring::checkOverflow(this_count, size_ - this_pos) +
            this_pos,
        that.data_,
        detail::fixedstring::checkOverflow(that_pos, that.size_),
        detail::fixedstring::checkOverflow(that_count, that.size_ - that_pos) +
            that_pos));
  }
  constexpr int compare(const Char *that) const noexcept
  {
    return compare(0u, size_, that, folly::constexpr_strlen(that));
  }
  constexpr int compare(Range<const Char *> that) const noexcept
  {
    return compare(0u, size_, that.begin(), that.size());
  }
  constexpr int compare(
      std::size_t this_pos, std::size_t this_count, const Char *that) const
      noexcept(false)
  {
    return compare(this_pos, this_count, that, folly::constexpr_strlen(that));
  }
  constexpr int compare(
      std::size_t this_pos,
      std::size_t this_count,
      Range<const Char *> that) const noexcept(false)
  {
    return compare(this_pos, this_count, that.begin(), that.size());
  }
  constexpr int compare(
      std::size_t this_pos,
      std::size_t this_count,
      const Char *that,
      std::size_t that_count) const noexcept(false)
  {
    return static_cast<int>(detail::fixedstring::compare_(
        data_,
        detail::fixedstring::checkOverflow(this_pos, size_),
        detail::fixedstring::checkOverflowOrNpos(this_count, size_ - this_pos) +
            this_pos,
        that,
        0u,
        that_count));
  }
  constexpr int compare(
      std::size_t this_pos,
      std::size_t this_count,
      Range<const Char *> that,
      std::size_t that_count) const noexcept(false)
  {
    return compare(
        this_pos,
        this_count,
        that.begin(),
        detail::fixedstring::checkOverflow(that_count, that.size()));
  }
  constexpr BasicFixedString substr(std::size_t pos) const noexcept(false)
  {
    return {*this, pos};
  }
  constexpr BasicFixedString substr(std::size_t pos, std::size_t count) const
      noexcept(false)
  {
    return {*this, pos, count};
  }
  template <std::size_t M>
  constexpr BasicFixedString &replace(
      const Char *first,
      const Char *last,
      const BasicFixedString<Char, M> &that) noexcept(false)
  {
    return replace(first - data_, last - first, that, 0u, that.size_);
  }
  template <std::size_t M>
  constexpr BasicFixedString &replace(
      std::size_t this_pos,
      std::size_t this_count,
      const BasicFixedString<Char, M> &that,
      std::size_t that_pos = 0u) noexcept(false)
  {
    return replace(this_pos, this_count, that, that_pos, that.size_ - that_pos);
  }
  template <std::size_t M>
  constexpr BasicFixedString &replace(
      std::size_t this_pos,
      std::size_t this_count,
      const BasicFixedString<Char, M> &that,
      std::size_t that_pos,
      std::size_t that_count) noexcept(false)
  {
    return *this = creplace(this_pos, this_count, that, that_pos, that_count);
  }
  constexpr BasicFixedString &replace(
      std::size_t this_pos,
      std::size_t this_count,
      const Char *that) noexcept(false)
  {
    return replace(this_pos, this_count, that, folly::constexpr_strlen(that));
  }
  constexpr BasicFixedString &replace(
      const Char *first, const Char *last, const Char *that) noexcept(false)
  {
    return replace(
        first - data_, last - first, that, folly::constexpr_strlen(that));
  }
  constexpr BasicFixedString &replace(
      std::size_t this_pos,
      std::size_t this_count,
      const Char *that,
      std::size_t that_count) noexcept(false)
  {
    return *this = detail::fixedstring::Helper::replace_<Char>(
               data_,
               size_,
               detail::fixedstring::checkOverflow(this_pos, size_),
               detail::fixedstring::checkOverflowOrNpos(
                   this_count, size_ - this_pos),
               that,
               0u,
               that_count,
               Indices{});
  }
  constexpr BasicFixedString &replace(
      std::size_t this_pos,
      std::size_t this_count,
      std::size_t that_count,
      Char ch) noexcept(false)
  {
    return replace(this_pos, this_count, BasicFixedString{that_count, ch});
  }
  constexpr BasicFixedString &replace(
      const Char *first,
      const Char *last,
      std::size_t that_count,
      Char ch) noexcept(false)
  {
    return replace(
        first - data_, last - first, BasicFixedString{that_count, ch});
  }
  constexpr BasicFixedString &replace(
      const Char *first,
      const Char *last,
      std::initializer_list<Char> il) noexcept(false)
  {
    return replace(first - data_, last - first, il.begin(), il.size());
  }
  template <std::size_t M>
  constexpr BasicFixedString<Char, N + M> creplace(
      std::size_t this_pos,
      std::size_t this_count,
      const BasicFixedString<Char, M> &that,
      std::size_t that_pos = 0u) const noexcept(false)
  {
    return creplace(
        this_pos,
        this_count,
        that,
        that_pos,
        that.size_ - detail::fixedstring::checkOverflow(that_pos, that.size_));
  }
  template <std::size_t M>
  constexpr BasicFixedString<Char, N + M> creplace(
      std::size_t this_pos,
      std::size_t this_count,
      const BasicFixedString<Char, M> &that,
      std::size_t that_pos,
      std::size_t that_count) const noexcept(false)
  {
    return detail::fixedstring::Helper::replace_<Char>(
        data_,
        size_,
        detail::fixedstring::checkOverflow(this_pos, size_),
        detail::fixedstring::checkOverflowOrNpos(this_count, size_ - this_pos),
        that.data_,
        detail::fixedstring::checkOverflow(that_pos, that.size_),
        detail::fixedstring::checkOverflowOrNpos(
            that_count, that.size_ - that_pos),
        std::make_index_sequence<N + M>{});
  }
  template <std::size_t M>
  constexpr BasicFixedString<Char, N + M> creplace(
      const Char *first,
      const Char *last,
      const BasicFixedString<Char, M> &that,
      std::size_t that_pos = 0u) const noexcept(false)
  {
    return creplace(
        first - data_,
        last - first,
        that,
        that_pos,
        that.size_ - detail::fixedstring::checkOverflow(that_pos, that.size_));
  }
  template <std::size_t M>
  constexpr BasicFixedString<Char, N + M> creplace(
      const Char *first,
      const Char *last,
      const BasicFixedString<Char, M> &that,
      std::size_t that_pos,
      std::size_t that_count) const noexcept(false)
  {
    return creplace(first - data_, last - first, that, that_pos, that_count);
  }
  template <std::size_t M>
  constexpr BasicFixedString<Char, N + M - 1u> creplace(
      std::size_t this_pos, std::size_t this_count, const Char (&that)[M]) const
      noexcept(false)
  {
    return creplace(this_pos, this_count, that, 0u, M - 1u);
  }
  template <std::size_t M>
  constexpr BasicFixedString<Char, N + M - 1u> creplace(
      std::size_t this_pos,
      std::size_t this_count,
      const Char (&that)[M],
      std::size_t that_pos,
      std::size_t that_count) const noexcept(false)
  {
    return detail::fixedstring::Helper::replace_<Char>(
        data_,
        size_,
        detail::fixedstring::checkOverflow(this_pos, size_),
        detail::fixedstring::checkOverflowOrNpos(this_count, size_ - this_pos),
        detail::fixedstring::checkNullTerminated(that),
        detail::fixedstring::checkOverflow(that_pos, M - 1u),
        detail::fixedstring::checkOverflowOrNpos(that_count, M - 1u - that_pos),
        std::make_index_sequence<N + M - 1u>{});
  }
  template <std::size_t M>
  constexpr BasicFixedString<Char, N + M - 1u> creplace(
      const Char *first, const Char *last, const Char (&that)[M]) const
      noexcept(false)
  {
    return creplace(first - data_, last - first, that, 0u, M - 1u);
  }
  template <std::size_t M>
  constexpr BasicFixedString<Char, N + M - 1u> creplace(
      const Char *first,
      const Char *last,
      const Char (&that)[M],
      std::size_t that_pos,
      std::size_t that_count) const noexcept(false)
  {
    return creplace(first - data_, last - first, that, that_pos, that_count);
  }
  constexpr std::size_t copy(Char *dest, std::size_t count) const noexcept
  {
    return copy(dest, count, 0u);
  }
  constexpr std::size_t copy(
      Char *dest, std::size_t count, std::size_t pos) const noexcept(false)
  {
    detail::fixedstring::checkOverflow(pos, size_);
    for (std::size_t i = 0u; i < count; ++i)
    {
      if (i + pos == size_)
      {
        return size_;
      }
      dest[i] = data_[i + pos];
    }
    return count;
  }
  constexpr void resize(std::size_t count) noexcept(false)
  {
    resize(count, Char(0));
  }
  constexpr void resize(std::size_t count, Char ch) noexcept(false)
  {
    detail::fixedstring::checkOverflow(count, N);
    if (count == size_)
    {
    }
    else if (count < size_)
    {
      size_ = count;
      data_[size_] = Char(0);
    }
    else
    {
      for (; size_ < count; ++size_)
      {
        data_[size_] = ch;
      }
      data_[size_] = Char(0);
    }
  }
  template <std::size_t M>
  constexpr std::size_t find(
      const BasicFixedString<Char, M> &that) const noexcept
  {
    return find(that, 0u);
  }
  template <std::size_t M>
  constexpr std::size_t find(
      const BasicFixedString<Char, M> &that, std::size_t pos) const
      noexcept(false)
  {
    return that.size_ <= size_ - detail::fixedstring::checkOverflow(pos, size_)
               ? detail::fixedstring::find_(data_, size_, that.data_, pos, that.size_)
               : npos;
  }
  constexpr std::size_t find(const Char *that) const noexcept
  {
    return find(that, 0u, folly::constexpr_strlen(that));
  }
  constexpr std::size_t find(const Char *that, std::size_t pos) const
      noexcept(false)
  {
    return find(that, pos, folly::constexpr_strlen(that));
  }
  constexpr std::size_t find(
      const Char *that, std::size_t pos, std::size_t count) const
      noexcept(false)
  {
    return count <= size_ - detail::fixedstring::checkOverflow(pos, size_)
               ? detail::fixedstring::find_(data_, size_, that, pos, count)
               : npos;
  }
  constexpr std::size_t find(Char ch) const noexcept
  {
    return find(ch, 0u);
  }
  constexpr std::size_t find(Char ch, std::size_t pos) const noexcept(false)
  {
    using A = const Char[1u];
    return 0u == size_ - detail::fixedstring::checkOverflow(pos, size_)
               ? npos
               : detail::fixedstring::find_(data_, size_, A{ch}, pos, 1u);
  }
  template <std::size_t M>
  constexpr std::size_t rfind(
      const BasicFixedString<Char, M> &that) const noexcept
  {
    return rfind(that, size_);
  }
  template <std::size_t M>
  constexpr std::size_t rfind(
      const BasicFixedString<Char, M> &that, std::size_t pos) const
      noexcept(false)
  {
    return that.size_ <= size_
               ? detail::fixedstring::rfind_(
                   data_,
                   that.data_,
                   folly::constexpr_min(
                       detail::fixedstring::checkOverflow(pos, size_),
                       size_ - that.size_),
                   that.size_)
               : npos;
  }
  constexpr std::size_t rfind(const Char *that) const noexcept
  {
    return rfind(that, size_, folly::constexpr_strlen(that));
  }
  constexpr std::size_t rfind(const Char *that, std::size_t pos) const
      noexcept(false)
  {
    return rfind(that, pos, folly::constexpr_strlen(that));
  }
  constexpr std::size_t rfind(
      const Char *that, std::size_t pos, std::size_t count) const
      noexcept(false)
  {
    return count <= size_
               ? detail::fixedstring::rfind_(
                   data_,
                   that,
                   folly::constexpr_min(
                       detail::fixedstring::checkOverflow(pos, size_),
                       size_ - count),
                   count)
               : npos;
  }
  constexpr std::size_t rfind(Char ch) const noexcept
  {
    return rfind(ch, size_);
  }
  constexpr std::size_t rfind(Char ch, std::size_t pos) const noexcept(false)
  {
    using A = const Char[1u];
    return 0u == size_
               ? npos
               : detail::fixedstring::rfind_(
                   data_,
                   A{ch},
                   folly::constexpr_min(
                       detail::fixedstring::checkOverflow(pos, size_), size_ - 1u),
                   1u);
  }
  template <std::size_t M>
  constexpr std::size_t find_first_of(
      const BasicFixedString<Char, M> &that) const noexcept
  {
    return find_first_of(that, 0u);
  }
  template <std::size_t M>
  constexpr std::size_t find_first_of(
      const BasicFixedString<Char, M> &that, std::size_t pos) const
      noexcept(false)
  {
    return size_ == detail::fixedstring::checkOverflow(pos, size_)
               ? npos
               : detail::fixedstring::find_first_of_(
                   data_, size_, that.data_, pos, that.size_);
  }
  constexpr std::size_t find_first_of(const Char *that) const noexcept
  {
    return find_first_of(that, 0u, folly::constexpr_strlen(that));
  }
  constexpr std::size_t find_first_of(const Char *that, std::size_t pos) const
      noexcept(false)
  {
    return find_first_of(that, pos, folly::constexpr_strlen(that));
  }
  constexpr std::size_t find_first_of(
      const Char *that, std::size_t pos, std::size_t count) const
      noexcept(false)
  {
    return size_ == detail::fixedstring::checkOverflow(pos, size_)
               ? npos
               : detail::fixedstring::find_first_of_(data_, size_, that, pos, count);
  }
  constexpr std::size_t find_first_of(Char ch) const noexcept
  {
    return find_first_of(ch, 0u);
  }
  constexpr std::size_t find_first_of(Char ch, std::size_t pos) const
      noexcept(false)
  {
    using A = const Char[1u];
    return size_ == detail::fixedstring::checkOverflow(pos, size_)
               ? npos
               : detail::fixedstring::find_first_of_(data_, size_, A{ch}, pos, 1u);
  }
  template <std::size_t M>
  constexpr std::size_t find_first_not_of(
      const BasicFixedString<Char, M> &that) const noexcept
  {
    return find_first_not_of(that, 0u);
  }
  template <std::size_t M>
  constexpr std::size_t find_first_not_of(
      const BasicFixedString<Char, M> &that, std::size_t pos) const
      noexcept(false)
  {
    return size_ == detail::fixedstring::checkOverflow(pos, size_)
               ? npos
               : detail::fixedstring::find_first_not_of_(
                   data_, size_, that.data_, pos, that.size_);
  }
  constexpr std::size_t find_first_not_of(const Char *that) const noexcept
  {
    return find_first_not_of(that, 0u, folly::constexpr_strlen(that));
  }
  constexpr std::size_t find_first_not_of(
      const Char *that, std::size_t pos) const noexcept(false)
  {
    return find_first_not_of(that, pos, folly::constexpr_strlen(that));
  }
  constexpr std::size_t find_first_not_of(
      const Char *that, std::size_t pos, std::size_t count) const
      noexcept(false)
  {
    return size_ == detail::fixedstring::checkOverflow(pos, size_)
               ? npos
               : detail::fixedstring::find_first_not_of_(
                   data_, size_, that, pos, count);
  }
  constexpr std::size_t find_first_not_of(Char ch) const noexcept
  {
    return find_first_not_of(ch, 0u);
  }
  constexpr std::size_t find_first_not_of(Char ch, std::size_t pos) const
      noexcept(false)
  {
    using A = const Char[1u];
    return 1u <= size_ - detail::fixedstring::checkOverflow(pos, size_)
               ? detail::fixedstring::find_first_not_of_(data_, size_, A{ch}, pos, 1u)
               : npos;
  }
  template <std::size_t M>
  constexpr std::size_t find_last_of(
      const BasicFixedString<Char, M> &that) const noexcept
  {
    return find_last_of(that, size_);
  }
  template <std::size_t M>
  constexpr std::size_t find_last_of(
      const BasicFixedString<Char, M> &that, std::size_t pos) const
      noexcept(false)
  {
    return 0u == size_
               ? npos
               : detail::fixedstring::find_last_of_(
                   data_,
                   that.data_,
                   folly::constexpr_min(
                       detail::fixedstring::checkOverflow(pos, size_), size_ - 1u),
                   that.size_);
  }
  constexpr std::size_t find_last_of(const Char *that) const noexcept
  {
    return find_last_of(that, size_, folly::constexpr_strlen(that));
  }
  constexpr std::size_t find_last_of(const Char *that, std::size_t pos) const
      noexcept(false)
  {
    return find_last_of(that, pos, folly::constexpr_strlen(that));
  }
  constexpr std::size_t find_last_of(
      const Char *that, std::size_t pos, std::size_t count) const
      noexcept(false)
  {
    return 0u == size_
               ? npos
               : detail::fixedstring::find_last_of_(
                   data_,
                   that,
                   folly::constexpr_min(
                       detail::fixedstring::checkOverflow(pos, size_), size_ - 1u),
                   count);
  }
  constexpr std::size_t find_last_of(Char ch) const noexcept
  {
    return find_last_of(ch, size_);
  }
  constexpr std::size_t find_last_of(Char ch, std::size_t pos) const
      noexcept(false)
  {
    using A = const Char[1u];
    return 0u == size_
               ? npos
               : detail::fixedstring::find_last_of_(
                   data_,
                   A{ch},
                   folly::constexpr_min(
                       detail::fixedstring::checkOverflow(pos, size_), size_ - 1u),
                   1u);
  }
  template <std::size_t M>
  constexpr std::size_t find_last_not_of(
      const BasicFixedString<Char, M> &that) const noexcept
  {
    return find_last_not_of(that, size_);
  }
  template <std::size_t M>
  constexpr std::size_t find_last_not_of(
      const BasicFixedString<Char, M> &that, std::size_t pos) const
      noexcept(false)
  {
    return 0u == size_
               ? npos
               : detail::fixedstring::find_last_not_of_(
                   data_,
                   that.data_,
                   folly::constexpr_min(
                       detail::fixedstring::checkOverflow(pos, size_), size_ - 1u),
                   that.size_);
  }
  constexpr std::size_t find_last_not_of(const Char *that) const noexcept
  {
    return find_last_not_of(that, size_, folly::constexpr_strlen(that));
  }
  constexpr std::size_t find_last_not_of(
      const Char *that, std::size_t pos) const noexcept(false)
  {
    return find_last_not_of(that, pos, folly::constexpr_strlen(that));
  }
  constexpr std::size_t find_last_not_of(
      const Char *that, std::size_t pos, std::size_t count) const
      noexcept(false)
  {
    return 0u == size_
               ? npos
               : detail::fixedstring::find_last_not_of_(
                   data_,
                   that,
                   folly::constexpr_min(
                       detail::fixedstring::checkOverflow(pos, size_), size_ - 1u),
                   count);
  }
  constexpr std::size_t find_last_not_of(Char ch) const noexcept
  {
    return find_last_not_of(ch, size_);
  }
  constexpr std::size_t find_last_not_of(Char ch, std::size_t pos) const
      noexcept(false)
  {
    using A = const Char[1u];
    return 0u == size_
               ? npos
               : detail::fixedstring::find_last_not_of_(
                   data_,
                   A{ch},
                   folly::constexpr_min(
                       detail::fixedstring::checkOverflow(pos, size_), size_ - 1u),
                   1u);
  }
  friend constexpr bool operator==(
      const Char *a, const BasicFixedString &b) noexcept
  {
    return detail::fixedstring::equal_(
        a, folly::constexpr_strlen(a), b.data_, b.size_);
  }
  friend constexpr bool operator==(
      const BasicFixedString &a, const Char *b) noexcept
  {
    return b == a;
  }
  friend constexpr bool operator==(
      Range<const Char *> a, const BasicFixedString &b) noexcept
  {
    return detail::fixedstring::equal_(a.begin(), a.size(), b.data_, b.size_);
  }
  friend constexpr bool operator==(
      const BasicFixedString &a, Range<const Char *> b) noexcept
  {
    return b == a;
  }
  friend constexpr bool operator!=(
      const Char *a, const BasicFixedString &b) noexcept
  {
    return !(a == b);
  }
  friend constexpr bool operator!=(
      const BasicFixedString &a, const Char *b) noexcept
  {
    return !(b == a);
  }
  friend constexpr bool operator!=(
      Range<const Char *> a, const BasicFixedString &b) noexcept
  {
    return !(a == b);
  }
  friend constexpr bool operator!=(
      const BasicFixedString &a, Range<const Char *> b) noexcept
  {
    return !(a == b);
  }
  friend constexpr bool operator<(
      const Char *a, const BasicFixedString &b) noexcept
  {
    return ordering::lt ==
           detail::fixedstring::compare_(
               a, 0u, folly::constexpr_strlen(a), b.data_, 0u, b.size_);
  }
  friend constexpr bool operator<(
      const BasicFixedString &a, const Char *b) noexcept
  {
    return ordering::lt ==
           detail::fixedstring::compare_(
               a.data_, 0u, a.size_, b, 0u, folly::constexpr_strlen(b));
  }
  friend constexpr bool operator<(
      Range<const Char *> a, const BasicFixedString &b) noexcept
  {
    return ordering::lt ==
           detail::fixedstring::compare_(
               a.begin(), 0u, a.size(), b.data_, 0u, b.size_);
  }
  friend constexpr bool operator<(
      const BasicFixedString &a, Range<const Char *> b) noexcept
  {
    return ordering::lt ==
           detail::fixedstring::compare_(
               a.data_, 0u, a.size_, b.begin(), 0u, b.size());
  }
  friend constexpr bool operator>(
      const Char *a, const BasicFixedString &b) noexcept
  {
    return b < a;
  }
  friend constexpr bool operator>(
      const BasicFixedString &a, const Char *b) noexcept
  {
    return b < a;
  }
  friend constexpr bool operator>(
      Range<const Char *> a, const BasicFixedString &b) noexcept
  {
    return b < a;
  }
  friend constexpr bool operator>(
      const BasicFixedString &a, Range<const Char *> b) noexcept
  {
    return b < a;
  }
  friend constexpr bool operator<=(
      const Char *a, const BasicFixedString &b) noexcept
  {
    return !(b < a);
  }
  friend constexpr bool operator<=(
      const BasicFixedString &a, const Char *b) noexcept
  {
    return !(b < a);
  }
  friend constexpr bool operator<=(
      Range<const Char *> const &a, const BasicFixedString &b) noexcept
  {
    return !(b < a);
  }
  friend constexpr bool operator<=(
      const BasicFixedString &a, Range<const Char *> b) noexcept
  {
    return !(b < a);
  }
  friend constexpr bool operator>=(
      const Char *a, const BasicFixedString &b) noexcept
  {
    return !(a < b);
  }
  friend constexpr bool operator>=(
      const BasicFixedString &a, const Char *b) noexcept
  {
    return !(a < b);
  }
  friend constexpr bool operator>=(
      Range<const Char *> a, const BasicFixedString &b) noexcept
  {
    return !(a < b);
  }
  friend constexpr bool operator>=(
      const BasicFixedString &a, Range<const Char *> const &b) noexcept
  {
    return !(a < b);
  }
  template <std::size_t M>
  friend constexpr BasicFixedString<Char, N + M - 1u> operator+(
      const Char (&a)[M], const BasicFixedString &b) noexcept
  {
    return detail::fixedstring::Helper::concat_<Char>(
        detail::fixedstring::checkNullTerminated(a),
        M - 1u,
        b.data_,
        b.size_,
        std::make_index_sequence<N + M - 1u>{});
  }
  template <std::size_t M>
  friend constexpr BasicFixedString<Char, N + M - 1u> operator+(
      const BasicFixedString &a, const Char (&b)[M]) noexcept
  {
    return detail::fixedstring::Helper::concat_<Char>(
        a.data_,
        a.size_,
        detail::fixedstring::checkNullTerminated(b),
        M - 1u,
        std::make_index_sequence<N + M - 1u>{});
  }
  friend constexpr BasicFixedString<Char, N + 1u> operator+(
      Char a, const BasicFixedString &b) noexcept
  {
    using A = const Char[2u];
    return detail::fixedstring::Helper::concat_<Char>(
        A{a, Char(0)},
        1u,
        b.data_,
        b.size_,
        std::make_index_sequence<N + 1u>{});
  }
  friend constexpr BasicFixedString<Char, N + 1u> operator+(
      const BasicFixedString &a, Char b) noexcept
  {
    using A = const Char[2u];
    return detail::fixedstring::Helper::concat_<Char>(
        a.data_,
        a.size_,
        A{b, Char(0)},
        1u,
        std::make_index_sequence<N + 1u>{});
  }
};
template <class C, std::size_t N>
inline std::basic_ostream<C> &operator<<(
    std::basic_ostream<C> &os, const BasicFixedString<C, N> &string)
{
  using StreamSize = decltype(os.width());
  os.write(string.begin(), static_cast<StreamSize>(string.size()));
  return os;
}
template <class Char, std::size_t A, std::size_t B>
constexpr bool operator==(
    const BasicFixedString<Char, A> &a,
    const BasicFixedString<Char, B> &b) noexcept
{
  return detail::fixedstring::equal_(
      detail::fixedstring::Helper::data_(a),
      a.size(),
      detail::fixedstring::Helper::data_(b),
      b.size());
}
template <class Char, std::size_t A, std::size_t B>
constexpr bool operator!=(
    const BasicFixedString<Char, A> &a, const BasicFixedString<Char, B> &b)
{
  return !(a == b);
}
template <class Char, std::size_t A, std::size_t B>
constexpr bool operator<(
    const BasicFixedString<Char, A> &a,
    const BasicFixedString<Char, B> &b) noexcept
{
  return ordering::lt ==
         detail::fixedstring::compare_(
             detail::fixedstring::Helper::data_(a),
             0u,
             a.size(),
             detail::fixedstring::Helper::data_(b),
             0u,
             b.size());
}
template <class Char, std::size_t A, std::size_t B>
constexpr bool operator>(
    const BasicFixedString<Char, A> &a,
    const BasicFixedString<Char, B> &b) noexcept
{
  return b < a;
}
template <class Char, std::size_t A, std::size_t B>
constexpr bool operator<=(
    const BasicFixedString<Char, A> &a,
    const BasicFixedString<Char, B> &b) noexcept
{
  return !(b < a);
}
template <class Char, std::size_t A, std::size_t B>
constexpr bool operator>=(
    const BasicFixedString<Char, A> &a,
    const BasicFixedString<Char, B> &b) noexcept
{
  return !(a < b);
}
template <class Char, std::size_t N, std::size_t M>
constexpr BasicFixedString<Char, N + M> operator+(
    const BasicFixedString<Char, N> &a,
    const BasicFixedString<Char, M> &b) noexcept
{
  return detail::fixedstring::Helper::concat_<Char>(
      detail::fixedstring::Helper::data_(a),
      a.size(),
      detail::fixedstring::Helper::data_(b),
      b.size(),
      std::make_index_sequence<N + M>{});
}
template <class Char, std::size_t N>
constexpr BasicFixedString<Char, N - 1u> makeFixedString(
    const Char (&a)[N]) noexcept
{
  return {a};
}
template <class Char, std::size_t N>
constexpr void swap(
    BasicFixedString<Char, N> &a, BasicFixedString<Char, N> &b) noexcept
{
  a.swap(b);
}
inline namespace literals
{
inline namespace string_literals
{
inline namespace
{
constexpr const std::size_t &npos = detail::fixedstring::FixedStringBase::npos;
}
template <class Char, Char... Cs>
constexpr BasicFixedString<Char, sizeof...(Cs)> operator"" _fs() noexcept
{
  const Char a[] = {Cs..., Char(0)};
  return {+a, sizeof...(Cs)};
}
constexpr FixedString<4> operator"" _fs4(const char *that, std::size_t count) noexcept(false)
{
  return {that, count};
}
constexpr FixedString<8> operator"" _fs8(const char *that, std::size_t count) noexcept(false)
{
  return {that, count};
}
constexpr FixedString<16> operator"" _fs16(const char *that, std::size_t count) noexcept(false)
{
  return {that, count};
}
constexpr FixedString<32> operator"" _fs32(const char *that, std::size_t count) noexcept(false)
{
  return {that, count};
}
constexpr FixedString<64> operator"" _fs64(const char *that, std::size_t count) noexcept(false)
{
  return {that, count};
}
constexpr FixedString<128> operator"" _fs128(const char *that, std::size_t count) noexcept(false)
{
  return {that, count};
}
} // namespace string_literals
} // namespace literals
} // namespace folly
