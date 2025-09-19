import Mathlib.Tactic.Linarith
import FunctionalProgramming.Lecture03

namespace Week03

-- Title of series that a user started but did not finish.
def Database.unfinished_for_user (db : Database) (uid : UserId) : List String := sorry
-- Next unwatched episode per series by user
-- E.g. series has episodes 0 through 5
-- User watched [0, 1, 3], return 4
def Database.next_episode_for_user (db : Database) (uid : UserId) : List (String × Nat) := sorry
-- Name of user with most views
def Database.user_with_most_views (db : Database) : Option String := sorry
-- Total cost for billing period N (i.e. `10*N - 10*N + 9`)
def Database.cost_for_bp (db : Database) (n : Nat) : Nat := sorry
-- Total revenue for billing period N (i.e. `10*N - 10*N + 9`)
def Database.revenue_for_bp (db : Database) (n : Nat) : Nat := sorry
-- Most profitable user for billing period N
def Database.most_profitable_user_for_bp (db : Database) (n : Nat) : Option String := sorry

end Week03
