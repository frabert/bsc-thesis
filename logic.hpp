#ifndef LOGIC_HPP
#define LOGIC_HPP

#include <type_traits>

namespace logic {
  // Nonterminal terms
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
  template <typename A, typename B, typename C, typename Enable = void>
  struct proof;

  template <typename... As, typename... Cs>
  struct proof<list<As...>, sequent<list<>, list<>>, list<Cs...>> {
    static constexpr bool value = false;
  };

  template <typename L, typename R, typename... Ls, typename... Rs,
            typename... As, typename... Cs>
  struct proof<list<As...>, sequent<list<L, Ls...>, list<R, Rs...>>,
               list<Cs...>,
               typename std::enable_if<satisfies<L, R>::value>::type> {
    static constexpr bool value = true;
  };

  template <typename L, typename R, typename... Ls, typename... Rs,
            typename... As, typename... Cs>
  struct proof<list<As...>, sequent<list<L, Ls...>, list<R, Rs...>>,
               list<Cs...>,
               typename std::enable_if<!(satisfies<L, R>::value)>::type> {
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
               list<Cs...>, typename std::enable_if<is_terminal<T>>::type> {
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
               list<Cs...>, typename std::enable_if<is_terminal<T>>::type> {
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
               list<Cs...>, typename std::enable_if<is_terminal<T>>::type> {
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
               typename std::enable_if<is_terminal<T>>::type> {
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

  template <typename... Ts> struct simplify<and_term<Ts...>, and_term<>> {
    using type = and_term<Ts...>;
  };

  template <typename T, T Value1, T Value2, typename T1, typename... Ts>
  struct simplify<and_term<less<T, Value1>, T1>,
                  and_term<less<T, Value2>, Ts...>> {
    using _temp = typename std::conditional<(Value2 < Value1), less<T, Value2>,
                                            less<T, Value1>>::type;
    using type = typename simplify<and_term<_temp, T1>, and_term<Ts...>>::type;
  };

  template <typename T, T Value1, T Value2, typename T1, typename... Ts>
  struct simplify<and_term<less<T, Value1>, T1>,
                  and_term<less_equal<T, Value2>, Ts...>> {
    using _temp =
     typename std::conditional<(Value2 < Value1), less_equal<T, Value2>,
                               less<T, Value1>>::type;
    using type = typename simplify<and_term<_temp, T1>, and_term<Ts...>>::type;
  };

  template <typename T, T Value1, T Value2, typename T1, typename... Ts>
  struct simplify<and_term<less_equal<T, Value1>, T1>,
                  and_term<less<T, Value2>, Ts...>> {
    using _temp =
     typename std::conditional<(Value1 < Value2), less_equal<T, Value1>,
                               less<T, Value2>>::type;
    using type = typename simplify<and_term<_temp, T1>, and_term<Ts...>>::type;
  };

  template <typename T, T Value1, T Value2, typename T1, typename... Ts>
  struct simplify<and_term<less_equal<T, Value1>, T1>,
                  and_term<less_equal<T, Value2>, Ts...>> {
    using _temp =
     typename std::conditional<(Value1 < Value2), less_equal<T, Value1>,
                               less_equal<T, Value2>>::type;
    using type = typename simplify<and_term<_temp, T1>, and_term<Ts...>>::type;
  };

  template <typename T, T Value1, T Value2, typename T1, typename... Ts>
  struct simplify<and_term<T1, not_term<less_equal<T, Value1>>>,
                  and_term<not_term<less_equal<T, Value2>>, Ts...>> {
    using _temp =
     typename std::conditional<(Value1 > Value2),
                               not_term<less_equal<T, Value1>>,
                               not_term<less_equal<T, Value2>>>::type;
    using type = typename simplify<and_term<T1, _temp>, and_term<Ts...>>::type;
  };

  template <typename T, T Value1, T Value2, typename T1, typename... Ts>
  struct simplify<and_term<T1, not_term<less_equal<T, Value1>>>,
                  and_term<not_term<less<T, Value2>>, Ts...>> {
    using _temp =
     typename std::conditional<(Value2 > Value1), not_term<less<T, Value2>>,
                               not_term<less_equal<T, Value1>>>::type;
    using type = typename simplify<and_term<T1, _temp>, and_term<Ts...>>::type;
  };

  template <typename T, T Value1, T Value2, typename T1, typename... Ts>
  struct simplify<and_term<T1, not_term<less<T, Value1>>>,
                  and_term<not_term<less_equal<T, Value2>>, Ts...>> {
    using _temp =
     typename std::conditional<(Value1 > Value2), not_term<less<T, Value1>>,
                               not_term<less_equal<T, Value2>>>::type;
    using type = typename simplify<and_term<T1, _temp>, and_term<Ts...>>::type;
  };

  template <typename T, T Value1, T Value2, typename T1, typename... Ts>
  struct simplify<and_term<T1, not_term<less<T, Value1>>>,
                  and_term<not_term<less<T, Value2>>, Ts...>> {
    using _temp =
     typename std::conditional<(Value1 > Value2), not_term<less<T, Value1>>,
                               not_term<less<T, Value2>>>::type;
    using type = typename simplify<and_term<T1, _temp>, and_term<Ts...>>::type;
  };
} // namespace logic

#endif