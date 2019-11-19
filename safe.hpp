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

  template <typename T> constexpr std::size_t constlog2(T v) {
    if (v < 0) {
      return 1 + log2(-(v / 2));
    } else if (v == 0) {
      return 0;
    } else {
      return 1 + log2(v / 2);
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

  template <typename T1, typename T2> struct cmin {
    using value =
     std::conditional_t<(bound_value<T1> < bound_value<T2>), T1, T2>;
  };

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

    template <typename C2> auto operator-(const safe<T, C2> &value) {
      auto res =
       safe<T, typename sub_type<typename normalize<T, typename C::type>::type,
                                 typename normalize<T, typename C2::type>::
                                  type>::type>::_unsafe_create(value);
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