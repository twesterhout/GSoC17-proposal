#include <utility>
#include <cassert>
#include <stdexcept>
#include <type_traits>

#include <experimental/string_view>


struct key_not_found_error : std::exception {
	auto what() const noexcept -> char const* override
	{ return _msg; }
private:
	static constexpr char const* _msg = "Key not found.";
};

constexpr char const* key_not_found_error::_msg;


namespace {

template < class _Static_map
         , bool _is_const 
         >
struct map_iterator {
	using type              = map_iterator<_Static_map, _is_const>;
	using difference_type   = typename _Static_map::difference_type;
	using value_type        = 
		std::conditional_t< _is_const
		                  , std::add_const_t<typename _Static_map::value_type>
		                  , typename _Static_map::value_type >;
	using iterator_category = std::random_access_iterator_tag;
	using reference         =
		std::conditional_t< _is_const
		                  , typename _Static_map::const_reference
		                  , typename _Static_map::reference >;
	using pointer           = std::add_pointer_t<value_type>;
	using size_type         = typename _Static_map::size_type;

private:
	using _const_iterator   = map_iterator<_Static_map, /*is_const =*/ true>;
	using _storage_type     = 
		std::conditional_t< _is_const
		                  , std::add_const_t<typename _Static_map::storage_type>
		                  , typename _Static_map::storage_type >;

	static constexpr size_type _size = _Static_map::size();
	_storage_type* _data;
	size_type      _i;
	
	constexpr auto _to_same_object( map_iterator const& x
	                              , map_iterator const& y ) const noexcept -> bool
	{ return x._data == y._data; }

public:
	constexpr map_iterator() noexcept : _data{ nullptr }, _i{ 0 } {}

	constexpr map_iterator(_storage_type& data, size_type const pos) noexcept
		: _data{ &data }, _i{ pos }
	{}

	constexpr map_iterator(map_iterator const& other) noexcept = default;
	constexpr map_iterator& operator=(map_iterator const& other) noexcept = default;

	__attribute__((always_inline))
	constexpr auto operator*() const -> reference
	{
		return _data != nullptr
			? ( _i < _size
			    ? _data->value(_i)
			    : (throw std::out_of_range{"Iterator not dereferenceable."}, _data->value(0))
			  )
			: (throw std::invalid_argument{"Iterator not dereferenceable."}, _data->value(0));
	}

	constexpr auto operator->() const -> pointer { return &(*(*this)); }

	constexpr auto operator++() noexcept -> map_iterator& { ++_i; return *this; }

	constexpr auto operator++(int) noexcept -> map_iterator
	{
		map_iterator saved{ *this };
		++(*this);
		return saved;
	}

	constexpr auto operator-(map_iterator const& other) const -> difference_type
	{
		return _to_same_object(*this, other)
			? (static_cast<difference_type>(_i) - static_cast<difference_type>(other._i))
			: (throw std::invalid_argument{"Iterators not comparable."}, 0);
	}

	constexpr auto operator==(map_iterator const& other) const noexcept -> bool
	{ return _to_same_object(*this, other) && (_i == other._i); }

	constexpr auto operator!=(map_iterator const& other) const noexcept -> bool
	{ return !(*this == other); }

	constexpr auto operator< (map_iterator const& other) const -> bool
	{ return (*this - other) <  0; }

	constexpr auto operator<=(map_iterator const& other) const -> bool
	{ return (*this - other) <= 0; }

	constexpr auto operator> (map_iterator const& other) const -> bool
	{ return (*this - other) >  0; }

	constexpr auto operator>=(map_iterator const& other) const -> bool
	{ return (*this - other) >= 0; }

	constexpr auto operator[](difference_type const n) const -> reference
	{ return *(*this + n); }

	constexpr operator _const_iterator() const noexcept { return {_data, _i}; }

	friend 
	constexpr auto swap(map_iterator& lhs, map_iterator& rhs) noexcept -> void
	{
		auto const _temp_idx = lhs._i;
		lhs._i = rhs._i;
		rhs._i = _temp_idx;

		auto const _temp_data = lhs._data;
		lhs._data = rhs._data;
		rhs._data = _temp_data;
	}

	friend 
	constexpr auto operator+ ( map_iterator    const& x
	                         , difference_type const  n ) noexcept -> map_iterator
	{ return {*(x._data), x._i + n}; }

	friend 
	constexpr auto operator+ ( difference_type const  n
	                         , map_iterator    const& x ) noexcept -> map_iterator
	{ return x + n; }

	friend 
	constexpr auto operator- ( map_iterator    const& x
	                         , difference_type const  n ) noexcept -> map_iterator
	{ return {*(x._data), x._i - n}; }
	
	friend 
	constexpr auto operator+=( map_iterator         & x
	                         , difference_type const  n ) noexcept -> map_iterator&
	{ return x = x + n; }

	friend 
	constexpr auto operator-=( map_iterator         & x
	                         , difference_type const  n ) noexcept -> map_iterator&
	{ return x = x - n; }
};

template <class _Static_map, bool _is_const>
constexpr typename _Static_map::size_type map_iterator<_Static_map, _is_const>::_size;

} // unnamed namespace


struct equal_c {
	template <class _Char>
	constexpr auto operator()( _Char const* const a
	                         , _Char const* const b ) const 
		noexcept( noexcept(std::declval<_Char>() == std::declval<_Char>()) 
		       && noexcept(std::declval<_Char>() != std::declval<_Char>()) )
	{
		std::size_t i = 0;
		while (a[i] != _Char{} && a[i] == b[i]) {
			++i;
		}
		return a[i] == _Char{} && b[i] == _Char{};
	}
};


namespace {

template <class _Char>
inline constexpr auto length_c(_Char const* const str) noexcept -> std::size_t
{
	std::size_t i = 0;
	while (str[i] != _Char{}) {
		++i;
	}
	return (i == 0) ? 0 : (i - 1);
}

template <class _Char>
inline constexpr auto crc32_hash(_Char const* const str) noexcept -> std::uint32_t
{
	constexpr std::uint32_t INITXOR  = 0xFFFFFFFF;
	constexpr std::uint32_t FINALXOR = 0xFFFFFFFF;
	constexpr std::uint32_t CRCPOLY  = 0xEDB88320;

	auto const l = length_c(str);
	auto crcreg  = INITXOR;

	for (std::size_t j = 0; j < l; ++j) {
		auto b = static_cast<std::make_unsigned_t<_Char>>(str[j]);
		for (std::size_t i = 0; i < 8 * sizeof(_Char); ++i) {
			if ((crcreg ^ b) & 1) {
				crcreg = (crcreg >> 1) ^ CRCPOLY;
			}
			else {
				crcreg >>= 1;
			}
			b >>= 1;
		}
	}

	return crcreg ^ FINALXOR;
}

template <class _Char>
inline constexpr auto simple_hash(_Char const* const str) noexcept
{
	std::size_t hash = 0;
	std::size_t i = 0;
	while (str[i] != _Char{}) {
		hash = 37 * hash + str[i];
		++i;
	}
	return hash;
}

} // unnamed namespace 


template <class _T, std::size_t _N, class = void>
struct hash_c;

template <class _T, std::size_t _N>
struct hash_c<_T, _N, std::enable_if_t<std::is_integral<_T>::value>> {
	constexpr auto operator()(_T const x) const noexcept -> std::size_t
	{ return static_cast<std::size_t>(x) % _N; }
};

template <std::size_t _N>
struct hash_c<char const*, _N> {
	constexpr auto operator()(char const* const x) const noexcept -> std::size_t
	{
		// return simple_hash(x) % _N;
		return static_cast<std::size_t>(crc32_hash(x)) % _N;
	}
};

template <std::size_t _N>
struct hash_c<std::experimental::string_view, _N> {
	constexpr auto operator()(std::experimental::string_view const& x) const noexcept
	{ return hash_c<char const*, _N>{}(x.data()); }
};


template < class _RAIterator, class _Pred>
inline constexpr auto find_if_c( _RAIterator&& first, _RAIterator&& last, _Pred&& p ) 
	noexcept( noexcept(std::declval<_RAIterator>() - std::declval<_RAIterator>()) 
	       && noexcept(std::declval<_RAIterator&>() = std::declval<_RAIterator>()) 
	       && noexcept(*std::declval<_RAIterator>()) 
	       && noexcept(++std::declval<_RAIterator>()) )
{
	auto const _count = last - first;
	auto i = first;
	std::remove_const_t<decltype(_count)> n = 0;
	while (n < _count && !p(*i)) {
		++n; ++i;
	}
	return n == _count ? last : i;
}


namespace {
template <bool... _Bs> struct _all;
template <> struct _all<> : std::true_type {};

template <bool _B, bool... _Bs>
struct _all<_B, _Bs...> : std::conditional_t<_B, _all<_Bs...>, std::false_type> {};
} // unnamed namespace


template < class _Key
         , class _Tp
         , size_t _N
         , class _Pred   = std::equal_to<_Key> 
         , class _Hasher = hash_c<_Key, _N>
         > 
class static_map {

public:
	using type                = static_map<_Key, _Tp, _N, _Pred, _Hasher>;

	using key_type            = _Key;
	using mapped_type         = _Tp;
	using key_equal           = _Pred;
	using hasher              = _Hasher;
	using value_type          = std::pair<key_type const, mapped_type>;
	using reference           = value_type &;
	using const_reference     = value_type const&;
	using iterator            = map_iterator<type, /*is_const =*/ false>;
	using const_iterator      = map_iterator<type, /*is_const =*/ true>;
	using difference_type     = std::ptrdiff_t;
	using size_type           = std::size_t;

private:
	struct _Storage {
	private:
		using _actual_value_type = value_type; 
		_actual_value_type _vs[_N];

		static constexpr auto make_node(const_reference value)
			noexcept( std::is_nothrow_copy_constructible<key_type>::value
			       && std::is_nothrow_copy_constructible<mapped_type>::value )
		{ return std::make_pair(value.first, value.second); }
	

	public:
		template <class... _Pair>
		constexpr _Storage(_Pair const&... values)
			noexcept(_all<noexcept(make_node(std::declval<_Pair const&>()))...>::value)
			: _vs{ make_node(values)... }
		{}

		constexpr auto value(size_type const i) const noexcept -> const_reference
		{ return _vs[i]; }

		constexpr auto value(size_type const i)       noexcept -> reference
		{ return _vs[i]; }
	};

public:
	using storage_type = _Storage;

private:
	key_equal    const _eq;
	hasher       const _hf;
	storage_type       _data;

private:
	__attribute__((always_inline))
	constexpr auto _lookup(key_type const& k) const 
		noexcept( noexcept(std::declval<hasher>()(std::declval<key_type>()))
		       && noexcept(std::declval<key_equal>()( std::declval<key_type>()
		                                            , std::declval<key_type>())) )
	{
		auto const guess = _hf(k);
		auto       i     = guess;

		while (i < _N && !_eq(_data.value(i).first, k)) { ++i; }
		if (i == _N) {
			i = 0;
			while (i < guess && !_eq(_data.value(i).first, k)) { ++i; }
			if (i == guess) return _N;
		}
		return i;
	}

public:
	template <class... _K, class... _V>
	constexpr static_map(std::pair<_K, _V> const&... values)
		noexcept( std::is_nothrow_constructible< storage_type
		                                       , std::pair<_K, _V> const&...>::value 
		       && std::is_nothrow_default_constructible<key_equal>::value
		       && std::is_nothrow_default_constructible<hasher>::value )
		: _eq{}, _hf{}, _data{ values... }
	{}

	template <class... _K, class... _V>
	constexpr static_map( key_equal equal, hasher hash_function
	                    , std::pair<_K, _V> const&... values )
		noexcept( std::is_nothrow_constructible< storage_type
		                                       , std::pair<_K, _V> const&...>::value 
		       && std::is_nothrow_move_constructible<key_equal>::value
		       && std::is_nothrow_move_constructible<hasher>::value )
		: _eq{ std::move(equal) }
		, _hf{ std::move(hash_function) }
		, _data{ values... }
	{}

	static constexpr auto size() noexcept -> size_type
	{ return _N; }

	constexpr auto begin() noexcept -> iterator
	{ return {_data, 0}; }

	constexpr auto   end() noexcept -> iterator
	{ return {_data, size()}; }

	constexpr auto cbegin() const noexcept -> const_iterator
	{ return {_data, 0}; }

	constexpr auto   cend() const noexcept -> const_iterator
	{ return {_data, size()}; }

	__attribute__((always_inline))
	constexpr auto find(key_type const& k) const 
		noexcept(noexcept(std::declval<static_map>()._lookup(std::declval<key_type>()))) 
		-> const_iterator
	{
		auto i = _lookup(k);
		return i == _N
			? cend()
			: const_iterator{_data, i};
	}

	constexpr auto count(key_type const& k) const 
		noexcept(noexcept(std::declval<static_map>().find(std::declval<key_type>())))
		-> size_type
	{ return find(k) == cend() ? 0 : 1; }

	__attribute__((always_inline))
	constexpr auto at(key_type const& k) const -> mapped_type const&
	{
		auto i = _lookup(k);
		return i != _N
			? _data.value(i).second
			: (throw key_not_found_error{}, _data.value(0).second);
	}

	__attribute__((always_inline))
	constexpr auto at(key_type const& k) -> mapped_type&
	{
		auto i = _lookup(k);
		return i != _N
			? _data.value(i).second
			: (throw key_not_found_error{}, _data.value(0).second);
	}

	constexpr auto operator[](key_type const& k) const -> mapped_type const&
	{ return at(k); }

	constexpr auto operator[](key_type const& k) -> mapped_type &
	{ return at(k); }
};



namespace {

template <std::size_t _N>
__attribute__((always_inline))
inline constexpr auto _insert( std::size_t const index
                             , std::size_t const guess
                             , std::size_t (&indices)[_N] ) noexcept
{
	auto i = guess;

	while (i < _N && indices[i] != _N) { ++i; }
	if (i == _N) {
		i = 0;
		while (i < guess && indices[i] != _N) { ++i; }
	}

	indices[i] = index;
}

template <std::size_t _N>
__attribute__((always_inline))
inline constexpr auto _init_impl( std::size_t (&indices)[_N] 
                                , std::pair<std::size_t, std::size_t> const& x ) noexcept
{ _insert(x.first, x.second, indices); }

template <std::size_t _N, class... _I>
__attribute__((always_inline))
inline constexpr auto _init_impl( std::size_t (&indices)[_N] 
                                , std::pair<std::size_t, std::size_t> const& x
                                , std::pair<_I, _I> const&... xs ) noexcept
{
	_insert(x.first, x.second, indices);
	_init_impl(indices, xs...);
}


template <std::size_t, class _T>
using _transform = _T;

template < class _K
         , class _V
         , class _Pred
         , class _Hasher
         , std::size_t _N
         , std::size_t... _Is
		 >
__attribute__((always_inline))
inline constexpr auto _initialise( std::pair<_K const, _V> const (&il)[_N]
                                 , _Pred&& equal, _Hasher&& hf
                                 , std::index_sequence<_Is...> )
	noexcept( noexcept(std::declval<_Hasher>()(std::declval<_K>())) 
	       && noexcept(std::is_nothrow_constructible
	                   < static_map<_K, _V, _N, _Pred, _Hasher> 
	                   , _Pred, _Hasher, _transform<_Is, std::pair<_K const, _V> const&>... 
	                   >::value) )
{
	std::size_t indices[_N] = {((void)_Is, _N)...};
	_init_impl(indices, std::make_pair(_Is, hf(il[_Is].first))...);

	return static_map<_K, _V, _N, _Pred, _Hasher>{ std::forward<_Pred>(equal)
	                                             , std::forward<_Hasher>(hf)
	                                             , il[indices[_Is]]... };
}

} // unnamed namespace

template < class _K
         , class _V
         , std::size_t _N
         , class _Pred = std::equal_to<_K>
         , class _Hasher = hash_c<_K, _N>
		 >
__attribute__((always_inline))
inline
constexpr
auto make_static_map( std::pair<_K const, _V> const (&il)[_N]
                    , _Pred&& equal = _Pred{}
                    , _Hasher&& hf = _Hasher{} )
	noexcept( noexcept(_initialise( std::declval<decltype(il)>()
	                              , std::declval<_Pred>()
	                              , std::declval<_Hasher>()
								  , std::make_index_sequence<_N>{})) )
{
	return _initialise( il
	                  , std::forward<_Pred>(equal)
	                  , std::forward<_Hasher>(hf)
	                  , std::make_index_sequence<_N>{} );
}


enum class weekday { sunday
                   , monday
                   , tuesday
                   , wednesday
                   , thursday
                   , friday
                   , saturday };

using std::experimental::string_view;
#define STRING_VIEW(str) std::experimental::string_view{str, sizeof(str)-1}

struct equal_string_view {
	constexpr
	auto operator()( string_view const& a
	               , string_view const& b ) const noexcept -> bool
	{ return equal_c{}(a.data(), b.data()); }
};

int main(void)
{
	{	
		// Compile-time stuff
		constexpr std::pair<int const, const char *> map_data[] =
			{ { 5, "apple"  }
			, { 8, "pear"   }
			, { 0, "banana" }
			};
		// Initialisation
		constexpr auto cmap = make_static_map(map_data);

		// No abort call in assembly
		if (!cmap[8]) abort();

		// These operations use hashing
		static_assert(equal_c{}(cmap[5], "apple"), "");
		static_assert(equal_c{}(cmap[8], "pear"), "");
		static_assert(equal_c{}(cmap[0], "banana"), "");

		// This fails to compile -- as expected.
		// constexpr auto foo = cmap[-1];
		
		// We need this because GCC does not support constexpr lambdas, yet.
		struct is_eight {
			constexpr auto operator()(std::pair<int, char const*> const& x)
				const noexcept
			{ return x.first == 8; }
		};

		// Iterators
		static_assert( find_if_c(cmap.cbegin(), cmap.cend(), is_eight{})
		               != cmap.cend(), "" );
	}
	{
		// Run-time stuff
		constexpr std::pair<int const, const char *> map_data[] =
			{ { 5, "apple"  }
			, { 8, "pear"   }
			, { 0, "banana" }
			};
		auto cmap = make_static_map(map_data);

		// No abort in assembly
		 if (!cmap.count(5)) abort();

		// Values are mutable !!
		auto& i = cmap.at(8);
		i = "orange";
		assert(equal_c{}(i, "orange"));

		// Iterators
		auto const it1 = cmap.find(8);
		assert(it1->first == 8);
	}
	{
		// Working with string_view
		constexpr std::pair<const std::experimental::string_view, weekday> 
			string_to_weekday[]
				{ { STRING_VIEW("sunday"),    weekday::sunday }
				, { STRING_VIEW("monday"),    weekday::monday }
				, { STRING_VIEW("tuesday"),   weekday::tuesday }
				, { STRING_VIEW("wednesday"), weekday::wednesday }
				, { STRING_VIEW("thursday"),  weekday::thursday }
				, { STRING_VIEW("friday"),    weekday::friday }
				, { STRING_VIEW("saturday"),  weekday::saturday }
				};
		constexpr auto to_weekday = make_static_map( string_to_weekday
		                                           , equal_string_view{} );

		static_assert(to_weekday[STRING_VIEW("sunday")] == weekday::sunday, "");
		static_assert(to_weekday[STRING_VIEW("monday")] == weekday::monday, "");
		static_assert(to_weekday[STRING_VIEW("tuesday")] == weekday::tuesday, "");
		static_assert(to_weekday[STRING_VIEW("wednesday")] == weekday::wednesday, "");
		static_assert(to_weekday[STRING_VIEW("thursday")] == weekday::thursday, "");
		static_assert(to_weekday[STRING_VIEW("friday")] == weekday::friday, "");
		static_assert(to_weekday[STRING_VIEW("saturday")] == weekday::saturday, "");

		if (!to_weekday.count(STRING_VIEW("sunday"))) abort();

		struct is_friday {
			constexpr auto operator()(std::pair< string_view const
			                                   , weekday > const& x)
				const noexcept -> bool
			{ return equal_c{}(x.first.data(), "friday"); }
		};

		// Lookup
		static_assert(to_weekday.find(STRING_VIEW("friday")) != to_weekday.cend(), "");
		static_assert(to_weekday.find(STRING_VIEW("__friday__")) == to_weekday.cend(), "" );
		// Linear search
		static_assert( find_if_c( to_weekday.cbegin(), to_weekday.cend()
		                        , is_friday{} ) != to_weekday.cend(), "" );
	}
	{
		// C-strings
		constexpr std::pair<char const* const, weekday> 
			string_to_weekday[]
				{ { "sunday",    weekday::sunday }
				, { "monday",    weekday::monday }
				, { "tuesday",   weekday::tuesday }
				, { "wednesday", weekday::wednesday }
				, { "thursday",  weekday::thursday }
				, { "friday",    weekday::friday }
				, { "saturday",  weekday::saturday }
				};
		constexpr auto to_weekday = make_static_map( string_to_weekday
		                                           , equal_c{} );
	}
	return 0;
}
