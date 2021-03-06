#define TEST(x, y) void x ## y (void)
#define EXPECT_STREQ(x, y) 
#define EXPECT_THROW(x, y)
#define EXPECT_EQ(x, y)
#define EXPECT_FALSE(x)
#define EXPECT_TRUE(x)

#include <header.h>
#include <CPortability.h>
#include <Constexpr.h>
#include <FixedString.h>
#include <FixedStringTest.cpp>

