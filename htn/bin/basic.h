
#ifndef _BASIC_
#define _BASIC_

#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <list>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#define MIN( a, b ) ( ( a ) < ( b ) ? ( a ) : ( b ) )
#define MAX( a, b ) ( ( a ) < ( b ) ? ( b ) : ( a ) )
#define SQR( a ) ( ( a ) * ( a ) )

#define PI 3.1415926535897932384

// insert all elements of a collection into a stream
template < typename T >
void insertAll( std::ostream &stream, const T &begin, const T &end ) {
	T i = begin;
	stream << "[";
	if ( i != end ) stream << *( i++ );
	while ( i != end ) stream << "," << *( i++ );
	stream << "]";
}

// insert a pair into a stream
template < typename T, typename U >
std::ostream &operator<<( std::ostream &stream, const std::pair< T, U > &p ) {
	return stream << "(" << p.first << "," << p.second << ")";
}

// insert a list into a stream
template < typename T >
std::ostream &operator<<( std::ostream &stream, const std::list< T > &l ) {
	insertAll( stream, l.begin(), l.end() );
	return stream;
}

// insert a map into a stream
template < typename T, typename U >
std::ostream &operator<<( std::ostream &stream, const std::map< T, U > &m ) {
	insertAll( stream, m.begin(), m.end() );
	return stream;
}

// pass a multiset to a stream
template < typename T >
std::ostream &operator<<( std::ostream &stream, const std::multiset< T > &s ) {
	insertAll( stream, s.begin(), s.end() );
	return stream;
}

// pass a set to a stream
template < typename T >
std::ostream &operator<<( std::ostream &stream, const std::set< T > &s ) {
	insertAll( stream, s.begin(), s.end() );
	return stream;
}

// pass a vector to a stream
template < typename T >
std::ostream &operator<<( std::ostream &stream, const std::vector< T > &v ) {
	insertAll( stream, v.begin(), v.end() );
	return stream;
}

#endif
