#include <header.h>

#define FS(x) ::folly::makeFixedString(x)
using namespace folly::string_literals;

void FixedStringCtorTest_Default(void) {
  constexpr folly::FixedString<42> s{};
  static_assert(s[0] == '\0', "");
  static_assert(s.size() == 0u, "");

  constexpr auto s2 = s;
  static_assert(s2[0] == '\0', "");
  static_assert(s2.size() == 0u, "");
}

void FixedStringCtorTest_FromPtrAndLength(void) {
  constexpr folly::FixedString<11> s{"hello world", 11};
  static_assert(s[0] == 'h', "");
  static_assert(s[10] == 'd', "");
  static_assert(s[11] == '\0', "");
  static_assert(s.size() == 11u, "");

  constexpr folly::FixedString<5> s2{"hello world", 5};
  static_assert(s2[0] == 'h', "");
  static_assert(s2[4] == 'o', "");
  static_assert(s2[5] == '\0', "");
  static_assert(s2.size() == 5u, "");

  constexpr folly::FixedString<20> s3{"hello world", 5};
  static_assert(s2[0] == 'h', "");
  static_assert(s2[4] == 'o', "");
  static_assert(s2[5] == '\0', "");
  static_assert(s2.size() == 5u, "");

  static_assert("hello" == s3, "");
  static_assert(s3 == "hello", "");
  static_assert(s3 == s2, "");
  static_assert("hell" != s3, "");
  static_assert(s3 != "helloooo", "");
  static_assert(!(s3 != s2), "");
}

void FixedStringCtorTest_FromUDL(void) {
  using namespace folly::literals;
#if defined(__GNUC__)
  constexpr auto x = "hello"_fs;
  static_assert(
      std::is_same<decltype(x), const folly::FixedString<5>>::value, "");
  static_assert(x[0] == 'h', "");
  static_assert(x[1] == 'e', "");
  static_assert(x[2] == 'l', "");
  static_assert(x[3] == 'l', "");
  static_assert(x[4] == 'o', "");
  static_assert(x[5] == '\0', "");
  static_assert(x.size() == 5u, "");
#endif

  constexpr auto y = "goodbye"_fs8;
  static_assert(
      std::is_same<decltype(y), const folly::FixedString<8>>::value, "");
  static_assert(y.size() == 7u, "");
  static_assert(y == "goodbye", "");

  constexpr auto z = "now is the time for all good llamas"_fs64;
  static_assert(
      std::is_same<decltype(z), const folly::FixedString<64>>::value, "");
  static_assert(z.size() == 35u, "");
  static_assert(z == "now is the time for all good llamas", "");
}

void FixedStringConcatTest_FromStringAndLiteral(void) {
  constexpr folly::FixedString<42> s{"hello world"};
  constexpr auto res = s + "!!!";
  static_assert(res.size() == 14u, "");
  static_assert(res == "hello world!!!", "");
}

void FixedStringConcatTest_FromTwoStrings(void) {
  constexpr folly::FixedString<42> s{"hello world"};
  constexpr auto res = s + "!!!";
  static_assert(res.size() == 14u, "");
  static_assert(res == "hello world!!!", "");
}

#ifdef BAD
void FixedStringEraseTest_CEraseTest(void) {
  constexpr auto x = FS("abcdefghijklmnopqrstuvwxyz"), y = x;
  constexpr auto tmp0 = x.cerase(x.size());
  static_assert(26u == tmp0.size(), "");
  static_assert(y == tmp0, "");
}
#endif
