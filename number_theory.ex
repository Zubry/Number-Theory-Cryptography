defmodule NumberTheory do
  @moduledoc """
    A collection of functions useful in number theory

    Examples:

    NumberTheory.chinese_remainder([3, 5, 7], [2, 3, 5])
      |> IO.puts
    # 17

  """

  @doc """
    Copy of the mod function from experimental_elixir, a fork of elixir

    In standard elixir, rem(-1, 10) = -1. We want mod(-1, 10) = 9, which this function implements
  """
  def mod(number, modulus) when is_integer(number) and is_integer(modulus) do
    case rem(number, modulus) do
      remainder when remainder > 0 and modulus < 0 or remainder < 0 and modulus > 0 ->
        remainder + modulus
      remainder ->
        remainder
    end
  end

  @doc """
    Finds the greatest common divisor of two integers

    When the left argument divides the right argument (i.e. a mod b == 0), the greatest common divisor is equal to the right argument
  """
  def gcd(a, b) when
    is_integer(a) and
    is_integer(b) and
    rem(a, b) == 0
  do
    b
  end

  @doc """
    Finds the greatest common divisor of two integers

    By the Euclidean Algorithm, the greatest common divisor of two integers a, b is equal to the greatest common divisor of b and the remainder of a divided by b. That is, GCD(a, b) = GCD(b, r), where r = a mod b.
  """
  def gcd(a, b) when
    is_integer(a) and
    is_integer(b)
  do
    r = rem(a, b)
    gcd(b, r)
  end

  @doc """
    Finds the greatest common divisor of a set of integers

    The greatest common divisor of a list is equal to
      gcd(l1, l2) |> gcd(l3) |> gcd(l4) |> ... |> gcd(ln)

    This can be computed by folding over (reducing) the tail (tl) of the list (everything except the first element) by the gcd function, passing in the head (hd, first element) to each gcd call as an accumulator
  """
  def gcd([h|t]) do
    t
      # Fold over the tail of l, getting the gcd of each element and the accumulator
      |> Enum.reduce(h, &gcd/2)
  end

  def combinations(_, 0) do
    [[]]
  end

  def combinations([], _) do
    []
  end

  @doc """
    Finds all combinations of a set l with r elements. Should return n choose r elements, where n = length(l)
  """
  def combinations([h|t], r) do
    test = combinations(t, r-1)
      |> Enum.map(fn(l) -> [h|l] end)

    test ++ combinations(t, r)
  end

  @doc """
    Determines whether or not two integers are coprime

    Two integers are coprime when their greatest common divisor is 1
  """
  def coprime?(a, b) when is_integer(a) and is_integer(b) do
    gcd(a, b) == 1
  end

  @doc """
    Determines whether or not a set of integers is pairwise coprime

    A set of integers is pairwise coprime if for all indices j < k in l, M_j is comprime to M_k

    In other words, if for all combinations of {a, b} in l, a is coprime to b, then l is pairwise comprime
  """
  def pairwise_coprime(l) when is_list(l) do
    combinations(l, 2)
      |> Enum.all?(fn(x) -> coprime?(hd(x), List.last(x)) end)
  end

  @doc """
    Calculates the reduced product of a set of integers

    An element of the reduced product R_k is equal to U / M_k, where U = M_0 * M_1 * ... * M_k
  """
  def reduced_product(l) when is_list(l) do
    # Calculate the product of the set
    # It isn't super readable, but &*/2 is a pointer (hence the "&") to the multiplication function, which has an arity of two, hence the "/2" at the end
    # So all we're doing is multiplying each element of l by the accumulator
    u = Enum.reduce(l, &*/2)

    # Divide u by each element of l to get the reduced product
    # Because m will always divide u, truncate the result, to ensure that we're dealing with integers
    Enum.map(l, fn(m) -> trunc(u / m) end)
  end

  @doc """
    Gets the quotient of two integers
  """
  def quotient(a, b) when is_integer(a) and is_integer(b) do
    trunc(a / b)
  end

  @doc """
    Gets the list of quotients of two integers
  """
  def quotients(a, 0) when is_integer(a) do
    []
  end

  def quotients(a, b) when is_integer(a) and is_integer(b) do
    r = rem(a, b)
    q = quotient(a, b)
    [q] ++ quotients(b, r)
  end

  @doc """
    Finds the mod-m reciprocal of n, i.e. mod_reciprocal(11, 38) == 7

    Uses the extended Euclidean algorithm
  """
  def mod_reciprocal(n, m) do
    # Create a list of quotients of m and n
    quotients(m, n)
      # The next element t_(n+1) is determined by
      # t_(n+1) = t_(n-1) - q_n * t_n
      # In order to implement this, we reduce the list of quotients, starting with the tuple {0, 1}, which represents t_0 = 0 and t_1 = 1.
      # Then, we calculate the tuple {t_1, t_2}, which is equal to {t_1, t_1 - q_1 * t_2}
      # Then, we calculate {t_2, t_3} etc
      # Until we get the tuple {t_(n-1), t_n}
      |> Enum.reduce({0, 1}, fn(q, {t1, t2}) ->      {t2, t1 - q * t2} end)
      # t_(n-1) is the mod reciprocal, so we only need to return the first element of the final tuple
      |> elem(0)
  end

  @doc """
    Calculates the magic tuple of a set of integers

    The magic tuple is a set of integers such that each G_j = R_j * mod_reciprocal(R_j, M_j)
  """
  def magic_tuple(m) do
    r = reduced_product(m)

    r
      |> Enum.zip(m)
      |> Enum.map(fn({r, m}) -> mod_reciprocal(r, m) end)
      |> Enum.zip(r)
      |> Enum.map(fn({rec, r}) -> rec * r end)
  end

  @doc """
    Calculates the magic tuple of a set of integers and reduces it by modulo-U, where U is the second argument
  """
  def magic_tuple(m, u) do
    magic_tuple(m)
      |> Enum.map(fn(m) -> rem(m, u) end)
  end

  @doc """
    Calculates the value for x such that
      x % m_i = x % r_i, for each given m_i in m and each given r_i in r
  """
  def chinese_remainder(r, m) when is_list(r) and is_list(m) do
    u = Enum.reduce(m, &*/2)

    magic_tuple(m)
      |> Enum.zip(r)
      |> Enum.map(fn({g, r}) -> g * r end)
      |> Enum.map(fn(g) -> mod(g, u) end)
      |> Enum.reduce(&+/2)
      |> mod(u)
  end
end
