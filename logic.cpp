#include "logic.hpp"
#include "safe.hpp"
#include "safe_array.hpp"

using namespace logic;

int main() {
  sequent<list<and_term<greater<int, 1>,
                        or_term<less_equal<int, 2>, less_equal<int, 3>>>>,
          list<or_term<and_term<greater<int, 1>, less_equal<int, 2>>,
                       and_term<greater<int, 1>, less_equal<int, 3>>>>>
   distrib;

  sequent<list<>, list<or_term<less<int, 1>, greater_equal<int, 1>>>> taut;

  sequent<list<or_term<less<int, 1>, less<int, 2>>>,
          list<or_term<less<int, 1>, less<int, 2>>>>
   taut_2;

  sequent<list<less<int, 1>>, list<less<int, 2>>> taut_3;

  sequent<list<and_term<less<int, 10>, greater<int, 5>>>,
          list<and_term<less<int, 20>, greater<int, 0>>>>
   taut_4;

  sequent<list<or_term<less<int, 1>, less<int, 2>>>,
          list<and_term<less<int, 1>, less<int, 2>>>>
   untrue;

  static_assert(truth_value<decltype(taut)>, "This formula is a tautology");
  static_assert(truth_value<decltype(taut_2)>, "This formula is a tautology");
  static_assert(truth_value<decltype(taut_3)>, "This formula is a tautology");
  static_assert(truth_value<decltype(taut_4)>, "This formula is a tautology");
  static_assert(truth_value<decltype(distrib)>, "Distributivity works");
  static_assert(!(truth_value<decltype(untrue)>),
                "This formula is not always true");

  constexpr bool val = truth_value<decltype(taut_4)>;

  auto s =
   safe<int, and_term<greater<int, 10>, less<int, 20>>>::make_safe<15>();
  auto s2 = make_safe<int, 15>();

  decltype(s) s3{s2};

  s3 = s2;

  auto s4 = s + s2;

  safe_array<int, 4> arr{1, 2, 3, 4};
  auto idx1 = safe<std::size_t, less<std::size_t, 3>>::make_safe<2>();
  int x = arr[idx1];

  auto idx2 = safe<std::size_t, and_term<greater<std::size_t, 1>,
                                         less<std::size_t, 5>>>::make_safe<3>();
  // The following line will not compile, as idx2 might cause an out-of-bounds
  // access int y = arr[idx2];

  return val ? 0 : 1;
  return 0;
}