#ifndef LOGIC_HPP
#define LOGIC_HPP

#include <type_traits>

namespace logic {
  // Nonterminal terms
  /*
   The `type` definition inside of the various terms is used to let users
   specify constraints using "short-hand" notation: for example,

      greater<int, 10>

   can be used instead of

      not_term<less_equal<int, 10>>

   even though `greater` is, strictly speaking, not part of the available
   constraints.

   When a term is already a "native" constraint, the `type` definition is just
   the constraint itself.
  */
  template <typename T> struct not_term {
    using type = not_term<typename T::type>;
  };
  template <typename... Ts> struct and_term {
    using type = and_term<typename Ts::type...>;
  };
  template <typename... Ts> struct or_term {
    using type = or_term<typename Ts::type...>;
  };

  template <typename T1, typename T2> struct concat;
  template <typename T1, typename T2>
  using concat_t = typename concat<T1, T2>::type;

  template <typename... T1, typename... T2>
  struct concat<and_term<T1...>, and_term<T2...>> {
    using type = and_term<T1..., T2...>;
  };

  template <typename... T1, typename... T2>
  struct concat<or_term<T1...>, or_term<T2...>> {
    using type = or_term<T1..., T2...>;
  };

  // Terminal terms
  template <typename T, T Val> struct less { using type = less<T, Val>; };
  template <typename T, T Val> struct less_equal {
    using type = less_equal<T, Val>;
  };

  template <typename T, T Val> struct greater {
    using type = not_term<less_equal<T, Val>>;
  };
  template <typename T, T Val> struct greater_equal {
    using type = not_term<less<T, Val>>;
  };

  template <typename T, T Min, T Max> struct between {
    using type = typename and_term<less<T, Max>, greater<T, Min>>::type;
  };

  template <typename T, T Min, T Max> struct between_inclusive {
    using type =
     typename and_term<less_equal<T, Max>, greater_equal<T, Min>>::type;
  };

  // Inference rules
  /*
   Implementation of the rules specified in section 2.2 of the thesis
  */
  template <typename L, typename R> struct satisfies;

  template <typename T1, typename T2, T1 Val1, T2 Val2>
  struct satisfies<less<T1, Val1>, less<T2, Val2>> {
    static constexpr bool value = Val1 <= Val2;
  };

  template <typename T1, typename T2, T1 Val1, T2 Val2>
  struct satisfies<less<T1, Val1>, less_equal<T2, Val2>> {
    static constexpr bool value = Val1 <= Val2;
  };

  template <typename T1, typename T2, T1 Val1, T2 Val2>
  struct satisfies<less_equal<T1, Val1>, less<T2, Val2>> {
    static constexpr bool value = Val1 < Val2;
  };

  template <typename T1, typename T2, T1 Val1, T2 Val2>
  struct satisfies<less_equal<T1, Val1>, less_equal<T2, Val2>> {
    static constexpr bool value = Val1 <= Val2;
  };

  template <typename... Ts> struct list {};

  template <typename L, typename R> struct sequent;

  template <typename... Ls, typename... Rs>
  struct sequent<list<Ls...>, list<Rs...>> {};

  // Axioms
  /*
   `proof` implements an algorithm for solving propositional calculus formulas
   using sequent calculus.

   `B` is the current sequent being evaluated, while `A` and `C` are helper
   lists used to implement the algorithm.

   The algorithm is as follows:
    1. The first element from the right side of the sequent is extracted.
       If it is not a terminal, it is subdivided (for example, an `or` term
       is subdivided and added to the right side of the sequent) and a new
       element is extracted. Repeat as long the extracted term is not terminal.
    2. The first element from the left side of the sequent is extracted.
       If it is not a terminal, it is subdivided (for example, an `and` term
       is subdivided and added to the left side of the sequent) and a new
       element is extracted. Repeat as long the extracted term is not terminal.
    3. If the element extracted from the left side can be used to prove the
       element extracted from the right side, the algorithm stops with a "true"
       value. Otherwise, the element from the left side is put into `A`. New
       elements will be extracted from the left side and put into `A` as long as
       the element on the right side cannot be proved. When the left side is
       empty, the element on the right side is put into `C` and the elements in
       `A` are put back into the left side.
    4. When both sides are empty, the algorithm stops with a "false" value.
  */
  template <typename A, typename B, typename C, typename Enable = void>
  struct proof;

  template <typename... As, typename... Cs>
  struct proof<list<As...>, sequent<list<>, list<>>, list<Cs...>> {
    static constexpr bool value = false;
  };

  template <typename L, typename R, typename... Ls, typename... Rs,
            typename... As, typename... Cs>
  struct proof<list<As...>, sequent<list<L, Ls...>, list<R, Rs...>>,
               list<Cs...>, std::enable_if_t<satisfies<L, R>::value>> {
    static constexpr bool value = true;
  };

  template <typename L, typename R, typename... Ls, typename... Rs,
            typename... As, typename... Cs>
  struct proof<list<As...>, sequent<list<L, Ls...>, list<R, Rs...>>,
               list<Cs...>, std::enable_if_t<!(satisfies<L, R>::value)>> {
    static constexpr bool value =
     proof<list<L, As...>, sequent<list<Ls...>, list<R, Cs..., Rs...>>,
           list<>>::value;
  };

  template <typename T> constexpr bool is_terminal = false;

  template <typename T, T Val> constexpr bool is_terminal<less<T, Val>> = true;

  template <typename T, T Val>
  constexpr bool is_terminal<less_equal<T, Val>> = true;

  template <typename T, typename... Ts, typename... As, typename... Ls,
            typename... Rs, typename... Cs>
  struct proof<list<As...>,
               sequent<list<T, Ls...>, list<or_term<Ts...>, Rs...>>,
               list<Cs...>, std::enable_if_t<is_terminal<T>>> {
    static constexpr bool value = proof<
     list<>,
     sequent<
      list<typename T::type, typename As::type..., typename Ls::type...>,
      list<typename Ts::type..., typename Cs::type..., typename Rs::type...>>,
     list<>>::value;
  };

  template <typename L, typename T, typename... As, typename... Ls,
            typename... Rs, typename... Cs>
  struct proof<list<As...>, sequent<list<L, Ls...>, list<not_term<T>, Rs...>>,
               list<Cs...>, std::enable_if_t<is_terminal<T>>> {
    static constexpr bool value =
     proof<list<>,
           sequent<list<typename L::type, typename T::type,
                        typename As::type..., typename Ls::type...>,
                   list<typename Cs::type..., typename Rs::type...>>,
           list<>>::value;
  };

  template <typename T, typename... Ts, typename... As, typename... Ls,
            typename... Rs, typename... Cs>
  struct proof<list<As...>,
               sequent<list<T, Ls...>, list<and_term<Ts...>, Rs...>>,
               list<Cs...>, std::enable_if_t<is_terminal<T>>> {
    static constexpr bool value =
     (proof<list<>,
            sequent<list<typename T::type, typename Ls::type...>,
                    list<typename Ts::type, typename Cs::type...,
                         typename Rs::type...>>,
            list<>>::value &&
      ...);
  };

  template <typename T, typename... As, typename... Ls, typename... Cs>
  struct proof<list<As...>, sequent<list<T, Ls...>, list<>>, list<Cs...>,
               std::enable_if_t<is_terminal<T>>> {
    static constexpr bool value =
     proof<list<typename T::type, typename As::type...>,
           sequent<list<typename Ls::type...>, list<>>,
           list<typename Cs::type...>>::value;
  };

  template <typename... Ts, typename... Ls, typename... Rs, typename... As,
            typename... Cs>
  struct proof<list<As...>, sequent<list<or_term<Ts...>, Ls...>, list<Rs...>>,
               list<Cs...>> {
    static constexpr bool value =
     (proof<list<>,
            sequent<list<typename Ts::type, typename As::type...,
                         typename Ls::type...>,
                    list<typename Cs::type..., typename Rs::type...>>,
            list<>>::value &&
      ...);
  };

  template <typename... Ts, typename... Ls, typename... Rs, typename... As,
            typename... Cs>
  struct proof<list<As...>, sequent<list<and_term<Ts...>, Ls...>, list<Rs...>>,
               list<Cs...>> {
    static constexpr bool value =
     proof<list<>,
           sequent<list<typename Ts::type..., typename As::type...,
                        typename Ls::type...>,
                   list<typename Cs::type..., typename Rs::type...>>,
           list<>>::value;
  };

  template <typename T, typename... Ls, typename... Rs, typename... As,
            typename... Cs>
  struct proof<list<As...>, sequent<list<not_term<T>, Ls...>, list<Rs...>>,
               list<Cs...>> {
    static constexpr bool value =
     proof<list<>,
           sequent<
            list<typename As::type..., typename Ls::type...>,
            list<typename T::type, typename Cs::type..., typename Rs::type...>>,
           list<>>::value;
  };

  template <typename... Ts, typename... Rs, typename... As, typename... Cs>
  struct proof<list<As...>, sequent<list<>, list<or_term<Ts...>, Rs...>>,
               list<Cs...>> {
    static constexpr bool value =
     proof<list<>,
           sequent<list<typename As::type...>,
                   list<typename Ts::type..., typename Cs::type...,
                        typename Rs::type...>>,
           list<>>::value;
  };

  template <typename T, typename... Rs, typename... As, typename... Cs>
  struct proof<list<As...>, sequent<list<>, list<not_term<T>, Rs...>>,
               list<Cs...>> {
    static constexpr bool value =
     proof<list<>,
           sequent<list<typename T::type, typename As::type...>,
                   list<typename Cs::type..., typename Rs::type...>>,
           list<>>::value;
  };

  template <typename... Ts, typename... Rs, typename... As, typename... Cs>
  struct proof<list<As...>, sequent<list<>, list<and_term<Ts...>, Rs...>>,
               list<Cs...>> {
    static constexpr bool value =
     (proof<list<>,
            sequent<list<typename As::type...>,
                    list<typename Ts::type, typename Cs::type...,
                         typename Rs::type...>>,
            list<>>::value &&
      ...);
  };

  template <typename T, typename... Rs, typename... As, typename... Cs>
  struct proof<list<As...>, sequent<list<>, list<T, Rs...>>, list<Cs...>> {
    static constexpr bool value =
     proof<list<>,
           sequent<list<typename As::type...>, list<typename Rs::type...>>,
           list<typename T::type, typename Cs::type...>>::value;
  };

  template <typename T>
  constexpr bool truth_value = proof<list<>, T, list<>>::value;

  template <typename T, typename C>
  constexpr bool is_acceptable(T Value, not_term<C> c) {
    return !(is_acceptable(Value, typename C::type{}));
  }

  template <typename T, typename... Cs>
  constexpr bool is_acceptable(T Value, and_term<Cs...> c) {
    return (is_acceptable(Value, typename Cs::type{}) && ...);
  }

  template <typename T, typename... Cs>
  constexpr bool is_acceptable(T Value, or_term<Cs...> c) {
    return (is_acceptable(Value, typename Cs::type{}) || ...);
  }

  template <typename T, T Constr>
  constexpr bool is_acceptable(T Value, less<T, Constr> c) {
    return Value < Constr;
  }

  template <typename T, T Constr>
  constexpr bool is_acceptable(T Value, less_equal<T, Constr> c) {
    return Value <= Constr;
  }

  template <typename T> constexpr T min(T a, T b) { return a < b ? a : b; }
  template <typename T, typename... Ts> constexpr T min(T a, Ts... b) {
    return min(a, min(b...));
  }

  template <typename T> constexpr T max(T a, T b) { return a > b ? a : b; }
  template <typename T, typename... Ts> constexpr T max(T a, Ts... b) {
    return max(a, max(b...));
  }

  template <typename T1, typename T2> struct simplify;
  template <typename T1, typename T2>
  using simplify_t = typename simplify<T1, T2>::type;

  template <typename... Ts> struct simplify<and_term<Ts...>, and_term<>> {
    using type = and_term<Ts...>;
  };

  template <typename T, T Value1, T Value2, typename T1, typename... Ts>
  struct simplify<and_term<less<T, Value1>, T1>,
                  and_term<less<T, Value2>, Ts...>> {
    using _temp =
     std::conditional_t<(Value2 < Value1), less<T, Value2>, less<T, Value1>>;
    using type = simplify_t<and_term<_temp, T1>, and_term<Ts...>>;
  };

  template <typename T, T Value1, T Value2, typename T1, typename... Ts>
  struct simplify<and_term<less<T, Value1>, T1>,
                  and_term<less_equal<T, Value2>, Ts...>> {
    using _temp = std::conditional_t<(Value2 < Value1), less_equal<T, Value2>,
                                     less<T, Value1>>;
    using type = simplify_t<and_term<_temp, T1>, and_term<Ts...>>;
  };

  template <typename T, T Value1, T Value2, typename T1, typename... Ts>
  struct simplify<and_term<less_equal<T, Value1>, T1>,
                  and_term<less<T, Value2>, Ts...>> {
    using _temp = std::conditional_t<(Value1 < Value2), less_equal<T, Value1>,
                                     less<T, Value2>>;
    using type = simplify_t<and_term<_temp, T1>, and_term<Ts...>>;
  };

  template <typename T, T Value1, T Value2, typename T1, typename... Ts>
  struct simplify<and_term<less_equal<T, Value1>, T1>,
                  and_term<less_equal<T, Value2>, Ts...>> {
    using _temp = std::conditional_t<(Value1 < Value2), less_equal<T, Value1>,
                                     less_equal<T, Value2>>;
    using type = simplify_t<and_term<_temp, T1>, and_term<Ts...>>;
  };

  template <typename T, T Value1, T Value2, typename T1, typename... Ts>
  struct simplify<and_term<T1, not_term<less_equal<T, Value1>>>,
                  and_term<not_term<less_equal<T, Value2>>, Ts...>> {
    using _temp =
     std::conditional_t<(Value1 > Value2), not_term<less_equal<T, Value1>>,
                        not_term<less_equal<T, Value2>>>;
    using type = simplify_t<and_term<T1, _temp>, and_term<Ts...>>;
  };

  template <typename T, T Value1, T Value2, typename T1, typename... Ts>
  struct simplify<and_term<T1, not_term<less_equal<T, Value1>>>,
                  and_term<not_term<less<T, Value2>>, Ts...>> {
    using _temp =
     std::conditional_t<(Value2 > Value1), not_term<less<T, Value2>>,
                        not_term<less_equal<T, Value1>>>;
    using type = simplify_t<and_term<T1, _temp>, and_term<Ts...>>;
  };

  template <typename T, T Value1, T Value2, typename T1, typename... Ts>
  struct simplify<and_term<T1, not_term<less<T, Value1>>>,
                  and_term<not_term<less_equal<T, Value2>>, Ts...>> {
    using _temp =
     std::conditional_t<(Value1 > Value2), not_term<less<T, Value1>>,
                        not_term<less_equal<T, Value2>>>;
    using type = simplify_t<and_term<T1, _temp>, and_term<Ts...>>;
  };

  template <typename T, T Value1, T Value2, typename T1, typename... Ts>
  struct simplify<and_term<T1, not_term<less<T, Value1>>>,
                  and_term<not_term<less<T, Value2>>, Ts...>> {
    using _temp =
     std::conditional_t<(Value1 > Value2), not_term<less<T, Value1>>,
                        not_term<less<T, Value2>>>;
    using type = simplify_t<and_term<T1, _temp>, and_term<Ts...>>;
  };
} // namespace logic

#endif