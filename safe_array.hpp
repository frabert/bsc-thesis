#ifndef SAFE_ARRAY_HPP
#define SAFE_ARRAY_HPP
#include "safe.hpp"
#include <array>
#include <cstddef>

namespace logic {
  template <typename T, std::size_t Size> struct safe_array {
    std::array<T, Size> m_data;
    using container = decltype(m_data);
    using value_type = T;
    using size_type = std::size_t;
    using difference_type = std::ptrdiff_t;
    using reference = value_type &;
    using const_reference = const T &;
    using pointer = value_type *;
    using const_pointer = const value_type *;
    using iterator = typename container::iterator;
    using const_iterator = typename container::const_iterator;
    using reverse_iterator = typename container::reverse_iterator;
    using const_reverse_iterator = typename container::const_reverse_iterator;

    using accessor_type = safe<std::size_t, less<std::size_t, Size>>;

    constexpr reference operator[](accessor_type index) {
      return m_data[index];
    }

    constexpr const_reference operator[](accessor_type index) const {
      return m_data[index];
    }

    constexpr std::array<T, Size> &array() const { return m_data; }
  };
} // namespace logic

#endif