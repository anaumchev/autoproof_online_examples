-- Node in a circular doubly-linked list
-- This example demonstrates multi-object invariants and update guards.

frozen class DLL_NODE

create
	make

feature {NONE} -- Initialization

	make
			-- Create a singleton node.
		note
			status: creator
		do
			left := Current
			right := Current
			-- Since `subjects' and `observers' have a simple structure,
			-- they are assigned automatically
		ensure
			singleton: left = Current
		end

feature -- Access

	left: DLL_NODE
			-- Left neighbor.
		note
			-- This update guard lets us update the attribute
			-- without notifying any observer expect `Current.left':
			guard: not_left
		attribute
		end

	right: DLL_NODE
			-- Right neighbor.
		note
			-- This update guard lets us update the attribute
			-- without notifying any observer expect `Current.right':
			guard: not_right
		attribute
		end

feature -- Modification

	insert_right (n: DLL_NODE)
			-- Insert node `n' to the right of the current node.
		note
			explicit: wrapping -- Do not automatically unwrap/wrap `Current'
		require
			n_exists: n /= Void
			n_singleton: n.left = n
			right_wrapped: right.is_wrapped
		local
			r: DLL_NODE
		do
			r := right
			unwrap_all (create {MML_SET [ANY]} & Current & r & n)

			n.set_right (r)
			n.set_left (Current)

			r.set_left (n)
			set_right (n)

			n.set_subjects (create {MML_SET [ANY]} & r & Current)
			n.set_observers (create {MML_SET [ANY]} & r & Current)
			set_subjects (create {MML_SET [ANY]} & left & n)
			set_observers (create {MML_SET [ANY]} & left & n)
			r.set_subjects (create {MML_SET [ANY]} & n & r.right)
			r.set_observers (create {MML_SET [ANY]} & n & r.right)
			wrap_all (create {MML_SET [ANY]} & Current & r & n)
		ensure
			modify (Current, right, n)
			n_left_set: right = n
			n_right_set: n.right = old right
		end

	remove
			-- Remove the current node from the list.
		note
			explicit: wrapping -- Do not automatically unwrap/wrap `Current'
		require
			left_wrapped: left.is_wrapped
			right_wrapped: right.is_wrapped
		local
			l, r: DLL_NODE
		do
			l := left
			r := right
			unwrap_all (create {MML_SET [ANY]} & Current & l & r)

			set_left (Current)
			set_right (Current)

			l.set_right (r)
			r.set_left (l)

			set_subjects (create {MML_SET [ANY]} & Current)
			set_observers (create {MML_SET [ANY]} & Current)
			l.set_subjects (create {MML_SET [ANY]} & l.left & r)
			l.set_observers (create {MML_SET [ANY]} & l.left & r)
			r.set_subjects (create {MML_SET [ANY]} & l & r.right)
			r.set_observers (create {MML_SET [ANY]} & l & r.right)
			wrap_all (create {MML_SET [ANY]} & Current & l & r)
		ensure
			modify (Current, left, right)
			singleton: right = Current
			old_left_wrapped: (old left).is_wrapped
			old_right_wrapped: (old right).is_wrapped
			neighbors_connected: (old left).right = old right
		end

feature {DLL_NODE} -- Implementation

	set_left (n: DLL_NODE)
			-- Set left neighbor to `n'.
		require
			open: is_open
			left_open: left.is_open
		do
			-- According to the update guard of attribute `left',
			-- other observers except `Current.left' cannot be invalidated by this update;
			-- this is why we only require that `Current.left' be open,
			-- and this is why we can perform list insertions and removals opening only three nodes
			-- (see `insert_right' and `remove').
			left := n
		ensure
			modify_field ("left", Current)
			left = n
		end

	set_right (n: DLL_NODE)
			-- Set right neighbor to `n'.
		require
			open: is_open
			right_open: right.is_open
		do
			-- According to the update guard of attribute `right',
			-- other observers except `Current.right' cannot be invalidated by this update;
			-- this is why we only require that `Current.right' be open,
			-- and this is why we can perform list insertions and removals opening only three nodes
			-- (see `insert_right' and `remove').			
			right := n
		ensure
			modify_field ("right", Current)
			right = n
		end

feature -- Specification

	not_left (new_left: DLL_NODE; o: ANY): BOOLEAN
			-- Is `o' different from `left'?
		note
			status: functional
		do
			Result := o /= left
		end

	not_right (new_right: DLL_NODE; o: ANY): BOOLEAN
			-- Is `o' different from `right'?
		note
			status: functional
		do
			Result := o /= right
		end

invariant
	left_exists: left /= Void
	right_exists: right /= Void
	subjects_structure: subjects = create {MML_SET [ANY]} & left & right
	observers_structure: observers = create {MML_SET [ANY]} & left & right
		-- These two invariant clauses depend on the state of other objects.
		-- They are only admissible because `left' and `right' are contained in `subjects'
		-- (try commenting out `subjects_structure' clause to see this).
	left_consistent: left.right = Current
	right_consistent: right.left = Current

end
