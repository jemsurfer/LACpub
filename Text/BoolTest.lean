namespace BoolTest

-- ANCHOR: not
def not : Bool → Bool
| true => false
| false => true
-- ANCHOR_END: not

-- ANCHOR: and
def and : Bool → Bool → Bool
| true , b => b
| false , _ => false
-- ANCHOR_END: and

-- ANCHOR: or
def or : Bool → Bool → Bool
| true , _ => true
| false , b => b
-- ANCHOR_END: or

-- scoped prefix:90 "!"     => not
-- scoped infixl:50 " && "  => and
-- scoped infixl:40 " || "  => or
end BoolTest

open Bool

--open scoped BoolTest
theorem b_dm2 : ∀ b c : Bool,
   (! (b && c)) = (!b || ! c) := by
intro b c
cases b
.  dsimp [and,not,or]
   --rfl --dsimp [and,not,or]
. rfl --dsimp [and,not,or]
