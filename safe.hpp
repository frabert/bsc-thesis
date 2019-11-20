#ifndef SAFE_HPP
#define SAFE_HPP

#include "logic.hpp"
#include <limits>
#include <optional>
#include <stdexcept>
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
  template <typename T1, typename T2>
  using normalize_t = typename normalize<T1, T2>::type;

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
  template <typename T1, typename T2>
  using sum_type_t = typename sum_type<T1, T2>::type;

  template <typename T> constexpr bool is_subtraction_safe(T lhs, T rhs) {
    if (lhs >= 0 && rhs < 0) {
      return std::numeric_limits<T>::max() + rhs >= lhs;
    } else if (lhs < 0 && rhs >= 0) {
      return std::numeric_limits<T>::lowest() + rhs <= lhs;
    }
    return true;
  }

  template <typename A, typename B> struct sub;

  template <typename T, T Value1, T Value2>
  struct sub<less<T, Value1>, less<T, Value2>> {
    static_assert(is_subtraction_safe(Value1, Value2), "Overflow detected");
    using type = less<T, Value1 - Value2>;
  };

  template <typename T, T Value1, T Value2>
  struct sub<less_equal<T, Value1>, less<T, Value2>> {
    static_assert(is_subtraction_safe(Value1, Value2), "Overflow detected");
    using type = less<T, Value1 - Value2>;
  };

  template <typename T, T Value1, T Value2>
  struct sub<less<T, Value1>, less_equal<T, Value2>> {
    static_assert(is_subtraction_safe(Value1, Value2), "Overflow detected");
    using type = less<T, Value1 - Value2>;
  };

  template <typename T, T Value1, T Value2>
  struct sub<less_equal<T, Value1>, less_equal<T, Value2>> {
    static_assert(is_subtraction_safe(Value1, Value2), "Overflow detected");
    using type = less_equal<T, Value1 - Value2>;
  };

  template <typename T, T Value1, T Value2>
  struct sub<not_term<less<T, Value1>>, not_term<less<T, Value2>>> {
    static_assert(is_subtraction_safe(Value1, Value2), "Overflow detected");
    using type = not_term<less<T, Value1 - Value2>>;
  };

  template <typename T, T Value1, T Value2>
  struct sub<not_term<less_equal<T, Value1>>, not_term<less<T, Value2>>> {
    static_assert(is_subtraction_safe(Value1, Value2), "Overflow detected");
    using type = not_term<less_equal<T, Value1 - Value2>>;
  };

  template <typename T, T Value1, T Value2>
  struct sub<not_term<less<T, Value1>>, not_term<less_equal<T, Value2>>> {
    static_assert(is_subtraction_safe(Value1, Value2), "Overflow detected");
    using type = not_term<less_equal<T, Value1 - Value2>>;
  };

  template <typename T, T Value1, T Value2>
  struct sub<not_term<less_equal<T, Value1>>, not_term<less_equal<T, Value2>>> {
    static_assert(is_subtraction_safe(Value1, Value2), "Overflow detected");
    using type = not_term<less_equal<T, Value1 - Value2>>;
  };

  template <typename L1, typename L2, typename R1, typename R2>
  struct sub<and_term<L1, L2>, and_term<R1, R2>> {
    using type =
     and_term<typename sum<L1, R1>::type, typename sum<L2, R2>::type>;
  };

  template <typename C1, typename C2> struct sub_type;

  template <typename T1, typename... T2s>
  struct sub_type<or_term<T1>, or_term<T2s...>> {
    using type = or_term<typename sum<T1, T2s>::type...>;
  };

  template <typename T1, typename... T1s, typename... T2s>
  struct sub_type<or_term<T1, T1s...>, or_term<T2s...>> {
    using type = typename concat<
     or_term<typename sub<T1, T2s>::type...>,
     typename sub_type<or_term<T1s...>, or_term<T2s...>>::type>::type;
  };
  template <typename T1, typename T2>
  using sub_type_t = typename sub_type<T1, T2>::type;

  template <typename T> constexpr std::size_t constlog2(T v) {
    if (v < 0) {
      return 1 + constlog2(-(v / 2));
    } else if (v == 0) {
      return 0;
    } else {
      return 1 + constlog2(v / 2);
    }
  }

  // Implementation of v overline
  template <typename T> struct invert;
  template <typename T, T Value> struct invert<less<T, Value>> {
    using value = less_equal<T, Value>;
  };
  template <typename T, T Value> struct invert<less_equal<T, Value>> {
    using value = less<T, Value>;
  };
  template <typename T> using invert_t = typename invert<T>::value;

  // Implementation of epsilon
  template <typename T> struct bound_value_s;
  template <typename T, T Value> struct bound_value_s<less<T, Value>> {
    static constexpr T value = Value;
  };
  template <typename T, T Value> struct bound_value_s<less_equal<T, Value>> {
    static constexpr T value = Value;
  };

  template <typename T> constexpr auto bound_value = bound_value_s<T>::value;

  template <typename T1, typename T2> struct cmax {
    using value =
     std::conditional_t<(bound_value<T1>> bound_value<T2>), T1, T2>;
  };
  template <typename T1, typename T2>
  using cmax_t = typename cmax<T1, T2>::value;

  template <typename T1, typename T2> struct cmin {
    using value =
     std::conditional_t<(bound_value<T1> < bound_value<T2>), T1, T2>;
  };
  template <typename T1, typename T2>
  using cmin_t = typename cmin<T1, T2>::value;

  // Implementation of M'
  template <typename T1, typename T2> struct prod;
  template <typename T, T Value1, T Value2>
  struct prod<less_equal<T, Value1>, less_equal<T, Value2>> {
    static_assert(constlog2(Value1) + constlog2(Value2) <=
                   constlog2(std::numeric_limits<T>::max()),
                  "Overflow detected");
    using value = less_equal<T, Value1 * Value2>;
  };
  template <typename T, T Value1, T Value2>
  struct prod<less<T, Value1>, less_equal<T, Value2>> {
    static_assert(constlog2(Value1) + constlog2(Value2) <=
                   constlog2(std::numeric_limits<T>::max()),
                  "Overflow detected");
    using value = less<T, Value1 * Value2>;
  };
  template <typename T, T Value1, T Value2>
  struct prod<less_equal<T, Value1>, less<T, Value2>> {
    static_assert(constlog2(Value1) + constlog2(Value2) <=
                   constlog2(std::numeric_limits<T>::max()),
                  "Overflow detected");
    using value = less<T, Value1 * Value2>;
  };
  template <typename T, T Value1, T Value2>
  struct prod<less<T, Value1>, less<T, Value2>> {
    static_assert(constlog2(Value1) + constlog2(Value2) <=
                   constlog2(std::numeric_limits<T>::max()),
                  "Overflow detected");
    using value = less<T, Value1 * Value2>;
  };
  template <typename T1, typename T2>
  using prod_t = typename prod<T1, T2>::value;

  // Implementation of M
  template <typename T1, typename T2, typename T3, typename T4, bool A, bool B,
            bool C, bool D>
  struct mul;
  template <typename T1, typename T2, typename T3, typename T4>
  struct mul<T1, T2, T3, T4, true, true, true, true> {
    using _temp1 = invert_t<T2>;
    using _temp2 = invert_t<T4>;
    using _temp3 = invert_t<prod_t<_temp1, _temp2>>;

    using value = and_term<prod_t<T1, T3>, not_term<_temp3>>;
  };
  template <typename T1, typename T2, typename T3, typename T4>
  struct mul<T1, T2, T3, T4, false, false, false, false> {
    using _temp1 = invert_t<T2>;
    using _temp2 = invert_t<T4>;
    using _temp3 = invert_t<prod_t<T1, T3>>;

    using value = and_term<prod_t<_temp1, _temp2>, not_term<_temp3>>;
  };
  template <typename T1, typename T2, typename T3, typename T4>
  struct mul<T1, T2, T3, T4, false, false, true, true> {
    using _temp1 = invert_t<T2>;
    using _temp2 = invert_t<T4>;
    using _temp3 = invert_t<prod_t<_temp1, T3>>;

    using value = and_term<prod_t<T1, _temp2>, not_term<_temp3>>;
  };
  template <typename T1, typename T2, typename T3, typename T4>
  struct mul<T1, T2, T3, T4, true, true, false, false> {
    using value = typename mul<T3, T4, T1, T2, false, false, true, true>::value;
  };
  template <typename T1, typename T2, typename T3, typename T4>
  struct mul<T1, T2, T3, T4, true, false, true, true> {
    using _temp1 = invert_t<T2>;
    using _temp2 = invert_t<prod_t<_temp1, T3>>;

    using value = and_term<prod_t<T1, T3>, not_term<_temp2>>;
  };
  template <typename T1, typename T2, typename T3, typename T4>
  struct mul<T1, T2, T3, T4, true, true, true, false> {
    using value = typename mul<T3, T4, T1, T2, true, false, true, true>::value;
  };
  template <typename T1, typename T2, typename T3, typename T4>
  struct mul<T1, T2, T3, T4, true, false, false, false> {
    using _temp1 = invert_t<T2>;
    using _temp2 = invert_t<T4>;
    using _temp3 = invert_t<prod_t<_temp1, _temp2>>;

    using value = and_term<prod_t<T1, _temp2>, not_term<_temp3>>;
  };
  template <typename T1, typename T2, typename T3, typename T4>
  struct mul<T1, T2, T3, T4, false, false, true, false> {
    using value =
     typename mul<T3, T4, T1, T2, false, false, false, true>::value;
  };
  template <typename T1, typename T2, typename T3, typename T4>
  struct mul<T1, T2, T3, T4, true, false, true, false> {
    using _temp1 = invert_t<T2>;
    using _temp2 = invert_t<T4>;
    using _temp3 = invert_t<prod_t<_temp1, _temp2>>;

    using _temp4 = prod_t<T1, T3>;
    using _temp5 = cmax_t<_temp4, _temp3>;

    using _temp6 = prod_t<T1, _temp2>;
    using _temp7 = prod_t<_temp1, T3>;
    using _temp8 = invert_t<cmin_t<_temp6, _temp7>>;

    using value = and_term<_temp5, not_term<_temp8>>;
  };
  template <typename T1, typename T2, typename T3, typename T4>
  using mul_t =
   typename mul<T1, T2, T3, T4, (bound_value<T1> >= 0), (bound_value<T2> >= 0),
                (bound_value<T3> >= 0), (bound_value<T4> >= 0)>::value;

  // Calculates M(phi_1, phi_2, phi_3, phi_4) given psi_1 and psi_2
  template <typename T1, typename T2> struct mul_helper;
  template <typename T1, typename T2, typename T3, typename T4>
  struct mul_helper<and_term<T1, not_term<T2>>, and_term<T3, not_term<T4>>> {
    using value = mul_t<T1, T2, T3, T4>;
  };
  template <typename T1, typename T2>
  using mul_helper_t = typename mul_helper<T1, T2>::value;

  template <typename C1, typename C2> struct mul_type;

  template <typename T1, typename... T2s>
  struct mul_type<or_term<T1>, or_term<T2s...>> {
    using type = or_term<mul_helper_t<T1, T2s>...>;
  };
  template <typename T1, typename T2>
  using mul_type_t = typename mul_type<T1, T2>::type;

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
      auto res = safe<
       T, sum_type_t<normalize_t<T, typename C::type>,
                     normalize_t<T, typename C2::type>>>::_unsafe_create(value);
      return res;
    }

    template <typename C2> auto operator-(const safe<T, C2> &value) {
      auto res = safe<
       T, sub_type_t<normalize_t<T, typename C::type>,
                     normalize_t<T, typename C2::type>>>::_unsafe_create(value);
      return res;
    }

    template <typename C2> auto operator*(const safe<T, C2> &value) {
      auto res = safe<
       T, mul_type_t<normalize_t<T, typename C::type>,
                     normalize_t<T, typename C2::type>>>::_unsafe_create(value);
      return res;
    }

    operator T() const { return m_value; }
  };

  template <typename T, T Value>
  constexpr safe<T, and_term<less_equal<T, Value>, greater_equal<T, Value>>>
  make_safe() {
    return safe<T, and_term<less_equal<T, Value>, greater_equal<T, Value>>>::
     template make_safe<Value>();
  }
} // namespace logic

#endif