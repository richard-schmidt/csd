namespace HeytAlg

class HeytAlg (N : Type v) : Type (v + 1) where
  le : N -> N -> Prop
  top : N
  bot : N
  meet : N -> N -> N -- inf
  join : N -> N -> N -- sup
  implies : N -> N -> N

  le_refl : ∀ a : N, le a a
  le_trans : ∀ a b c : N, le a b ∧ le b c → le a c
  le_symm : ∀ a b : N, le a b ∧ le b a ↔ a = b

  bot_univ : ∀ a : N, le bot a
  top_univ : ∀ a : N, le a top

  join_comm : ∀ a b : N, join a b = join b a
  join_idemp : ∀ a : N, join a a = a
  join_intro : ∀ a b : N, le a (join a b) ∧ le b (join a b)
  join_univ : ∀ x a b : N, le (join a b) x ↔ le a x ∧ le b x
  join_bot : ∀ a : N, join a bot = a
  join_top : ∀ a : N, join a top = top
  join_assoc : ∀ a b c : N, join a (join b c) = join (join a b) c

  meet_comm : ∀ a b : N, meet a b = meet b a
  meet_idemp : ∀ a : N, meet a a = a
  meet_intro :  ∀ a b : N, le (meet a b) a ∧ le (meet a b) b
  meet_univ : ∀ a b c : N, le a b ∧ le a c ↔ le a (meet b c)
  meet_bot : ∀ a : N, meet bot a = bot
  meet_top : ∀ a : N, meet top a = a
  meet_assoc : ∀ a b c : N, meet (meet a b) c = meet a (meet b c)

  join_absorb : ∀ a b : N, meet a (join a b) = a
  meet_absorb : ∀ a b : N, join a (meet a b) = a

  implies_univ : ∀ x a b : N, le (meet x a) b ↔ le x (implies a b)

scoped infixl:65 " ⊔ " => HeytAlg.join
scoped infixl:75 " ⊓ " => HeytAlg.meet
scoped infixr:50 " ⊸ " => HeytAlg.implies
scoped infix:50 " ≤ "  => HeytAlg.le
scoped prefix:80 "¬" => fun x => x ⊸ HeytAlg.bot

section HeytAlgThm

variable {N : Type u} [HeytAlg N] {x a b c : N}

theorem modus_ponens (a b : N) : (a ⊓ (a ⊸ b)) ≤ b := by
rw [HeytAlg.meet_comm, HeytAlg.implies_univ (a ⊸ b) a b]
simp [HeytAlg.le_refl (a ⊸ b)]

theorem meet_monotone (h : a ≤ b) (c : N) : a ⊓ c ≤ b ⊓ c := by
rw [← HeytAlg.meet_univ]
have h1 : a ⊓ c ≤ b := by
  have h2 := (HeytAlg.meet_intro a c).1
  apply HeytAlg.le_trans (a ⊓ c) a b
  exact ⟨ h2 , h ⟩
exact ⟨ h1, (HeytAlg.meet_intro a c).2 ⟩

theorem composition_law (a b c : N) : (a ⊸ b) ⊓ (b ⊸ c) ≤ (a ⊸ c) := by
rw [← HeytAlg.implies_univ]
rw [HeytAlg.meet_assoc, HeytAlg.meet_comm, HeytAlg.meet_assoc, HeytAlg.meet_comm]
have h1 := meet_monotone (modus_ponens a b) (b ⊸ c)
have h2 := modus_ponens b c
apply HeytAlg.le_trans _ (b ⊓ (b ⊸ c))
exact ⟨ h1, h2 ⟩

theorem currying (a b c : N) : ((a ⊓ b) ⊸ c) = (a ⊸ b ⊸ c) := by
rw [← HeytAlg.le_symm]
constructor
· rw [← HeytAlg.implies_univ, ← HeytAlg.implies_univ, HeytAlg.meet_assoc, HeytAlg.meet_comm]
  exact modus_ponens (a ⊓ b) _
· rw [← HeytAlg.implies_univ, ← HeytAlg.meet_assoc, HeytAlg.implies_univ, HeytAlg.implies_univ]
  exact HeytAlg.le_refl _

theorem implies_monotone (a b c : N) (h : b ≤ c) : (a ⊸ b) ≤ (a ⊸ c) := by
rw [← HeytAlg.implies_univ, HeytAlg.meet_comm]
have h1 : a ⊓ (a ⊸ b) ≤ b := modus_ponens _ _
have h2 := HeytAlg.le_trans (a ⊓ (a ⊸ b)) b c
apply h2 ⟨ h1, h ⟩

theorem implies_increasing (a b : N) : b ≤ (a ⊸ b) := by
rw [← HeytAlg.implies_univ]
obtain ⟨ h, _⟩ := HeytAlg.meet_intro b a
exact h

theorem implies_idempotent (a b : N) : (a ⊸ a ⊸ b) = (a ⊸ b) := by
rw [← HeytAlg.le_symm]
constructor
· rw [← HeytAlg.implies_univ, HeytAlg.meet_comm, ← currying, HeytAlg.meet_idemp]
  exact modus_ponens a b
· rw [← currying, HeytAlg.meet_idemp]
  exact HeytAlg.le_refl _

theorem implies_antimonotone (a b c : N) (h : b ≤ c) : (c ⊸ a) ≤ (b ⊸ a) := by
rw [← HeytAlg.implies_univ]
have h1 : b ⊓ (c ⊸ a) ≤ c ⊓ (c ⊸ a) := by
  apply meet_monotone
  exact h
have h2 : c ⊓ (c ⊸ a) ≤ a := by exact modus_ponens _ _
rw [HeytAlg.meet_comm] at h1
apply HeytAlg.le_trans
exact ⟨ h1, h2 ⟩

theorem implies_self_adjoint (a b c : N) : b ≤ (c ⊸ a) ↔ c ≤ (b ⊸ a) := by
constructor
· intro h
  rw [← HeytAlg.implies_univ, HeytAlg.meet_comm _ c , HeytAlg.implies_univ] at h
  exact h
· intro h
  rw [← HeytAlg.implies_univ, HeytAlg.meet_comm c _, HeytAlg.implies_univ] at h
  exact h

end HeytAlgThm

end HeytAlg
