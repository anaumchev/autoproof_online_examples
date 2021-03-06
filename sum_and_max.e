-- Calculating the sum and the maximum of array elements.
-- (From the VSTTE 2010 verification competition).

class
	SUM_AND_MAX

feature

	sum_and_max (a: SIMPLE_ARRAY [INTEGER]): TUPLE [sum, max: INTEGER]
			-- Calculate sum and maximum of array `a'.
		require
			a_not_void: a /= Void
			natural_numbers: ∀ ai: 1 |..| a.count ¦ a.sequence [ai] >= 0
		local
			i: INTEGER
			sum, max: INTEGER
		do
			from
				i := 1
			invariant
				i_in_range: 1 <= i and i <= a.count + 1
				sum_and_max_not_negative: sum >= 0 and max >= 0
				partial_sum_and_max: sum <= (i - 1) * max
			until
				i > a.count
			loop
				if a [i] > max then
					max := a [i]
				end
				sum := sum + a [i]
				i := i + 1
			end
			Result := [sum, max]
		ensure
			sum_in_range: Result.sum <= a.count * Result.max
		end

end
