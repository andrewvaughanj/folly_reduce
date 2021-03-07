#include <cassert>
#include <functional>
#include <stdexcept>
namespace folly {
template <typename T> constexpr T constexpr_max(T b...) { return b; }
template <typename T> constexpr T constexpr_min(T a, T b) {
  return b < a ? b : a;
}
constexpr auto kIsDebug = 1;
template <typename, typename Args> void throw_exception(Args);
template <class Iter> struct Range {
  constexpr Range(Iter start, size_t size) : b_(start), e_(start + size) {}
  template <class Container>
  constexpr Range(Container &container)
      : Range(container.data(), container.size()) {}
  constexpr Iter begin() const { return b_; }
  constexpr Iter end() const { return e_; }
  Iter b_;
  Iter e_;
};
typedef Range<const char *> StringPiece;
enum ordering { lt = -1, eq, gt };
} // namespace folly
