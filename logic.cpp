#include "logic.hpp"
#include "safe.hpp"
#include "safe_array.hpp"

int main() {
  logic::sequent<
   logic::list<logic::and_term<
    logic::greater<int, 1>,
    logic::or_term<logic::less_equal<int, 2>, logic::less_equal<int, 3>>>>,
   logic::list<logic::or_term<
    logic::and_term<logic::greater<int, 1>, logic::less_equal<int, 2>>,
    logic::and_term<logic::greater<int, 1>, logic::less_equal<int, 3>>>>>
   distrib;

  logic::sequent<logic::list<>,
                 logic::list<logic::or_term<logic::less<int, 1>,
                                            logic::greater_equal<int, 1>>>>
   taut;

  logic::sequent<
   logic::list<logic::or_term<logic::less<int, 1>, logic::less<int, 2>>>,
   logic::list<logic::or_term<logic::less<int, 1>, logic::less<int, 2>>>>
   taut_2;

  logic::sequent<logic::list<logic::less<int, 1>>,
                 logic::list<logic::less<int, 2>>>
   taut_3;

  logic::sequent<
   logic::list<logic::and_term<logic::less<int, 10>, logic::greater<int, 5>>>,
   logic::list<logic::and_term<logic::less<int, 20>, logic::greater<int, 0>>>>
   taut_4;

  logic::sequent<
   logic::list<logic::or_term<logic::less<int, 1>, logic::less<int, 2>>>,
   logic::list<logic::and_term<logic::less<int, 1>, logic::less<int, 2>>>>
   untrue;

  static_assert(logic::truth_value<decltype(taut)>,
                "This formula is a tautology");
  static_assert(logic::truth_value<decltype(taut_2)>,
                "This formula is a tautology");
  static_assert(logic::truth_value<decltype(taut_3)>,
                "This formula is a tautology");
  static_assert(logic::truth_value<decltype(taut_4)>,
                "This formula is a tautology");
  static_assert(logic::truth_value<decltype(distrib)>, "Distributivity works");
  static_assert(!(logic::truth_value<decltype(untrue)>),
                "This formula is not always true");

  constexpr bool val = logic::truth_value<decltype(taut_4)>;

  auto s =
   logic::safe<int, logic::and_term<logic::greater<int, 10>,
                                    logic::less<int, 20>>>::make_safe<15>();
  auto s2 = logic::make_safe<int, 15>();

  decltype(s) s3{s2};

  s3 = s2;

  auto s4 = s + s2;

  logic::safe_array<int, 4> arr{1, 2, 3, 4};
  auto v1 =
   logic::safe<std::size_t, logic::less<std::size_t, 3>>::make_safe<2>();
  int x = arr[v1];

  return val ? 0 : 1;
  return 0;
}