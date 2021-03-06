#include <memory>
namespace folly {
namespace detail {
template <typename Char>
constexpr size_t constexpr_strlen_internal(Char s, int) {
  return __builtin_strlen(s);
}
} // namespace detail
template <typename Char> constexpr size_t constexpr_strlen(Char s) {
  return detail::constexpr_strlen_internal(s, 1);
}
template <class, size_t> struct BasicFixedString;
template <size_t N> using FixedString = BasicFixedString<char, N>;
namespace detail {
namespace fixedstring {
constexpr size_t checkOverflow(size_t i, size_t) { return i; }
constexpr size_t checkOverflowIfDebug(size_t i, size_t) { return i; }
template <class Char, size_t N>
constexpr Char (&checkNullTerminated(Char (&a)[N]))[] {
  return constexpr_strlen(a) ? a : a;
}
struct Helper {
  template <class Char, class Left, class Right, size_t... Is>
  static constexpr BasicFixedString<Char, sizeof...(Is)>
  concat_(Left, size_t left_count, Right, size_t right_count,
          std::index_sequence<Is...>) {
    return {1, left_count, 1, right_count};
  }
};
} // namespace fixedstring
} // namespace detail
template <class Char, size_t N> struct BasicFixedString {
  Char data_[N + 1];
  size_t size_;
  using Indices = std::make_index_sequence<N>;
  template <class That, size_t... Is>
  constexpr BasicFixedString(That that, size_t size, std::index_sequence<Is...>)
      : data_{Is < size ? that[Is] : Char()...}, size_(size) {}
  template <class Left, class Right>
  constexpr BasicFixedString(Left, size_t left_size, Right, size_t right_size)
      : data_{}, size_{left_size + right_size} {}
  constexpr BasicFixedString() : data_{}, size_{} {}
  template <size_t M>
  constexpr BasicFixedString(const Char (&that)[M])
      : BasicFixedString{detail::fixedstring::checkNullTerminated(that),
                         M - 1} {}
  constexpr BasicFixedString(const Char *that, size_t count)
      : BasicFixedString{that, detail::fixedstring::checkOverflow(count, 1),
                         Indices{}} {}
  constexpr size_t size() const { return size_; }
  constexpr Char operator[](size_t i) const {
    return data_[detail::fixedstring::checkOverflowIfDebug(i, 1)];
  }
  constexpr BasicFixedString cerase(size_t) const {
    using A = Char[1];
    return A{};
  }
  friend constexpr int operator==(const Char *, BasicFixedString) { return 1; }
  friend constexpr int operator==(BasicFixedString, const Char *) { return 1; }
  friend constexpr int operator!=(const Char *, BasicFixedString) { return !0; }
  friend constexpr int operator!=(BasicFixedString, const Char *) { return !0; }
  template <size_t M>
  friend constexpr BasicFixedString<Char, N + M - 1>
  operator+(BasicFixedString a, const Char (&)[M]) {
    return detail::fixedstring::Helper::concat_<Char>(
        1, a.size_, 1, M - 1, std::make_index_sequence<N + M - 1>{});
  }
};
template <class Char, size_t A, size_t B>
constexpr int operator==(BasicFixedString<Char, A>,
                         BasicFixedString<Char, B> b) {
  return b.size();
}
template <class Char, size_t A, size_t B>
constexpr int operator!=(BasicFixedString<Char, A>, BasicFixedString<Char, B>) {
  return !1;
}
template <class Char, size_t N>
constexpr BasicFixedString<Char, 1> makeFixedString(Char (&)[N]) {
  return {};
}
inline namespace literals {
namespace string_literals {
template <class Char, Char... Cs>
constexpr BasicFixedString<Char, sizeof...(Cs)> operator"" _fs() {
  Char a[]{Cs...};
  return {a, sizeof...(Cs)};
}
constexpr FixedString<8> operator"" _fs8(const char *that, size_t count) {
  return {that, count};
}
constexpr FixedString<64> operator"" _fs64(const char *that, size_t count) {
  return {that, count};
}
} // namespace string_literals
} // namespace literals
} // namespace folly
