#include <limits>
#include <optional>
#include <type_traits>

namespace logic {
  template <typename T> constexpr bool is_addition_safe(T lhs, T rhs) {
    if (lhs >= 0 && rhs >= 0) {
      return std::numeric_limits<T>::max() - lhs > rhs;
    } else if (lhs < 0 && rhs < 0) {
      return lhs > std::numeric_limits<T>::lowest() - rhs;
    }
    return true;
  }

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

  template <typename A, typename B> struct sum;

  template <typename T, T Value1, T Value2>
  struct sum<less<T, Value1>, less<T, Value2>> {
    static_assert(is_addition_safe(Value1, Value2), "Overflow detected");
    using type = less<T, Value1 + Value2>;
  };

  template <typename T, T Value1, T Value2>
  struct sum<less_equal<T, Value1>, less<T, Value2>> {
    static_assert(is_addition_safe(Value1, Value2), "Overflow detected");
    using type = less<T, Value1 + Value2>;
  };

  template <typename T, T Value1, T Value2>
  struct sum<less<T, Value1>, less_equal<T, Value2>> {
    static_assert(is_addition_safe(Value1, Value2), "Overflow detected");
    using type = less<T, Value1 + Value2>;
  };

  template <typename T, T Value1, T Value2>
  struct sum<less_equal<T, Value1>, less_equal<T, Value2>> {
    static_assert(is_addition_safe(Value1, Value2), "Overflow detected");
    using type = less_equal<T, Value1 + Value2>;
  };

  template <typename T, T Value1, T Value2>
  struct sum<not_term<less<T, Value1>>, not_term<less<T, Value2>>> {
    static_assert(is_addition_safe(Value1, Value2), "Overflow detected");
    using type = not_term<less<T, Value1 + Value2>>;
  };

  template <typename T, T Value1, T Value2>
  struct sum<not_term<less_equal<T, Value1>>, not_term<less<T, Value2>>> {
    static_assert(is_addition_safe(Value1, Value2), "Overflow detected");
    using type = not_term<less_equal<T, Value1 + Value2>>;
  };

  template <typename T, T Value1, T Value2>
  struct sum<not_term<less<T, Value1>>, not_term<less_equal<T, Value2>>> {
    static_assert(is_addition_safe(Value1, Value2), "Overflow detected");
    using type = not_term<less_equal<T, Value1 + Value2>>;
  };

  template <typename T, T Value1, T Value2>
  struct sum<not_term<less_equal<T, Value1>>, not_term<less_equal<T, Value2>>> {
    static_assert(is_addition_safe(Value1, Value2), "Overflow detected");
    using type = not_term<less_equal<T, Value1 + Value2>>;
  };

  template <typename L1, typename L2, typename R1, typename R2>
  struct sum<and_term<L1, L2>, and_term<R1, R2>> {
    using type =
     and_term<typename sum<L1, R1>::type, typename sum<L2, R2>::type>;
  };

  template <typename T1, typename T2> struct normalize {
    using type = or_term<typename simplify<
     and_term<less_equal<T1, std::numeric_limits<T1>::max()>,
              not_term<less<T1, std::numeric_limits<T1>::lowest()>>>,
     and_term<T2>>::type>;
  };
  template <typename T, typename... Ts> struct normalize<T, and_term<Ts...>> {
    using type = or_term<typename simplify<
     and_term<less_equal<T, std::numeric_limits<T>::max()>,
              not_term<less<T, std::numeric_limits<T>::lowest()>>>,
     and_term<Ts...>>::type>;
  };
  template <typename T, typename... Ts> struct normalize<T, or_term<Ts...>> {
    using type = or_term<typename simplify<
     and_term<less_equal<T, std::numeric_limits<T>::max()>,
              not_term<less<T, std::numeric_limits<T>::lowest()>>>,
     Ts>::type...>;
  };

  template <typename C1, typename C2> struct sum_type;

  template <typename T1, typename... T2s>
  struct sum_type<or_term<T1>, or_term<T2s...>> {
    using type = or_term<typename sum<T1, T2s>::type...>;
  };

  template <typename T1, typename... T1s, typename... T2s>
  struct sum_type<or_term<T1, T1s...>, or_term<T2s...>> {
    using type = typename concat<
     or_term<typename sum<T1, T2s>::type...>,
     typename sum_type<or_term<T1s...>, or_term<T2s...>>::type>::type;
  };

  template <typename T,
            typename C =
             and_term<less_equal<T, std::numeric_limits<T>::max()>,
                      not_term<less<T, std::numeric_limits<T>::lowest()>>>>
  class safe {
    T m_value;
    // For internal use only
    safe() {}

  public:
    static safe _unsafe_create(T value) {
      safe s{};
      s.m_value = value;
      return s;
    }

    template <T Value> static constexpr safe make_safe() {
      static_assert(is_acceptable(Value, C{}), "Value is not acceptable");
      safe s{};
      s.m_value = Value;
      return s;
    }

#if 0
        static constexpr std::optional<safe> make_safe(T value) {
            if(is_acceptable(value, C{})) {
                safe s{};
                s.m_value = value;
                return std::make_optional(s);
            } else {
                return {};
            }
        }
#endif

    template <typename C2> safe(safe<T, C2> value) : m_value(value) {
      static_assert(truth_value<sequent<list<C2>, list<C>>>, "Invalid value");
    }

    safe(T value) : m_value(value) {
      if (!is_acceptable(value, C{})) {
        throw std::range_error{"value"};
      }
    }

    template <typename C2> safe &operator=(const safe<T, C2> &value) {
      static_assert(truth_value<sequent<list<C2>, list<C>>>, "Invalid value");
      m_value = value;
      return *this;
    }

    template <typename C2> auto operator+(const safe<T, C2> &value) {
      auto res =
       safe<T, typename sum_type<typename normalize<T, typename C::type>::type,
                                 typename normalize<T, typename C2::type>::
                                  type>::type>::_unsafe_create(value);
      return res;
    }

    operator T() const { return m_value; }

    template <typename C2> operator safe<T, C2>() const {
      return safe<T, C2>(*this);
    }
  };

  template <typename T, T Value>
  constexpr safe<T, and_term<less_equal<T, Value>, greater_equal<T, Value>>>
  make_safe() {
    return safe<T, and_term<less_equal<T, Value>, greater_equal<T, Value>>>::
     template make_safe<Value>();
  }
} // namespace logic

template <typename T> struct WhichType;

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

  return val ? 0 : 1;
  return 0;
}