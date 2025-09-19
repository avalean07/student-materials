import Mathlib.Tactic.Linarith
import Std.Data.HashMap

namespace Week03

-- Update on LMS: grades coming soon.

-- Resource on asking good questions: https://jvns.ca/blog/good-questions/

/-
structure UserStr where
  user_id : Nat
  name : String

inductive UserInd where
  | mk : Nat → String → UserInd

def userStrToInd : UserStr → UserInd :=
  fun us => UserInd.mk us.user_id us.name

def userStrToInd' : UserStr → UserInd
  | ⟨ ui, n ⟩ => UserInd.mk ui n

def userIndToStr : UserInd → UserStr
  | UserInd.mk ui n => ⟨ ui, n ⟩

def userIndToStr' : UserInd → UserStr
  | UserInd.mk ui n => { user_id := ui, name := n }
-/

abbrev UserId := Nat
abbrev SeriesId := Nat

inductive Billing where
  | per_ten_days
  | per_view

-- Our billing periods run days 0-9, 10-19, etc.

def Billing.price (num_views : Nat) : Billing → Nat
  | per_ten_days => 200
  | per_view => 10 * num_views

def cost (num_views : Nat) := 3 * num_views

structure User where
  name : String

structure Series where
  series_id : SeriesId
  title : String
  num_episodes : Nat

structure View where
  user_id : UserId
  series_id : SeriesId
  episode : Nat

structure Database where
  users : Std.HashMap UserId User
  series : List Series
  views : List View

def lecture_db : Database := {
  users := Std.HashMap.ofList [⟨0, ⟨"Alice"⟩⟩, ⟨1, ⟨"Bob"⟩⟩],
  series := [pokemon, good_omens],
  views := [⟨0, 100, 0⟩, ⟨1, 100, 5⟩, ⟨1, 200, 5⟩, ⟨0, 100, 1⟩, ⟨0, 100, 2⟩]
}
where
  pokemon : Series := ⟨ 100, "Pokemon", 1000 ⟩
  good_omens : Series := ⟨ 200, "Good Omens", 12 ⟩

#check List.map
#eval [0, 1, 2].map (fun n => n + 1)
#eval [0, 1, 2].map (· + 1)
#check List.filter
#eval [0, 1, 2].filter (· % 2 == 0)
#check List.head?
#print Option
#eval ([].head? : Option Nat)
#eval [0, 1, 2].head?
#check List.mergeSort
#eval [2, 1, 0].mergeSort
#eval ["Alice", "Bob", "Charlie"].mergeSort (fun s1 s2 => s1.length ≤ s2.length)
#check Option.map
#eval (some 5).map (· + 3)
#check Option.getD
#eval none.getD 0
#check List.reduceOption

/-
def Database.usernames : Database → List String
  | ⟨ [], _, _ ⟩ => []
  | ⟨ u :: us, ss, vs ⟩ => u.name :: (⟨ us, ss, vs ⟩ : Database).usernames
-/
def Database.usernames (db : Database) : List String :=
  db.users.toList.map (·.2.name)

#eval lecture_db.usernames

def Database.lookup_series (db : Database) (sid : SeriesId) : Option Series :=
  (db.series.filter (·.series_id = sid)).head?

#check Std.HashMap.get
#check Std.HashMap.get!
#check Std.HashMap.get?

def Database.lookup_user (db : Database) (uid : UserId) : Option User :=
  db.users.get? uid

def deduplicate : List ℕ → List ℕ
  | [] => []
  | [n] => [n]
  | (n :: m :: ns) =>
      if n = m
      then deduplicate (m :: ns)
      else n :: deduplicate (m :: ns)

/-
def Database.series_watched_by (db : Database) (uid : UserId) : List String :=
    helper db []
  where helper (db' : Database) (sids : List SeriesId) : List String :=
    match db' with
    | ⟨ us, ss, [] ⟩ => sorry
    | ⟨ us, ss, (v :: vs) ⟩ =>
        if v.user_id = uid
        then helper ⟨ us, ss, vs ⟩ (v.series_id :: sids)
        else helper ⟨ us, ss, vs ⟩ sids
-/

def Database.series_watched_by (db : Database) (uid : UserId) : List String :=
  let vs_by_u := db.views.filter (·.user_id = uid)
  let sids := vs_by_u.map (·.series_id)
  let dedup_sids := deduplicate sids.mergeSort
  let ss := (dedup_sids.map (fun sid => db.lookup_series sid)).reduceOption
  ss.map (·.title)

#eval lecture_db.series_watched_by 0
#eval lecture_db.series_watched_by 1

def Database.users_who_watched (db : Database) (sid : SeriesId) : List String :=
  let vs_by_s := db.views.filter (·.series_id = sid)
  let uids := vs_by_s.map (·.user_id)
  let dedup_uids := deduplicate uids.mergeSort
  let us := (dedup_uids.map (fun uid => db.lookup_user uid)).reduceOption
  us.map (·.name)

#eval lecture_db.users_who_watched 100
#eval lecture_db.users_who_watched 200

#check List.foldl

def Database.views_per_user (db : Database) : Std.HashMap UserId Nat :=
    db.views.foldl (fun m v => m.modify v.user_id (· + 1)) zeroPerUser
  where zeroPerUser := db.users.map (fun _ _ => 0)

#eval lecture_db.views_per_user

end Week03
