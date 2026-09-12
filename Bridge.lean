import MyProject.HardyLittlewood

/-!
# Bridge: connecting the RNS-sieve development to the Challenge vocabulary

Restates `Challenge.lean`'s vocabulary over `Finset ℤ`, and fills its two
genuine gaps — `hardyLittlewoodConstant` and `hardyLittlewoodConstant_pos` —
by transporting the fully-proved `RNS.*` results from
`MyProject/HardyLittlewood.lean` (stated over `Finset Nat`).
-/

open Finset Filter

abbrev Constellation : Type := Finset ℤ

def omega (H : Constellation) (p : ℕ) : ℕ :=
  (H.image (fun (h : ℤ) => (h : ZMod p))).card

def IsAdmissible (H : Constellation) : Prop :=
  ∀ p : ℕ, p.Prime → omega H p < p

lemma omega_shift (H : Constellation) (c : ℤ) (p : ℕ) :
    omega (H.image (· + c)) p = omega H p := by
  unfold omega
  rw [Finset.image_image]
  have hcomp : (fun h : ℤ => (h : ZMod p)) ∘ (· + c)
      = (· + (c : ZMod p)) ∘ (fun h : ℤ => (h : ZMod p)) := by
    funext h
    simp only [Function.comp_apply]
    push_cast
    ring
  rw [hcomp, ← Finset.image_image]
  exact Finset.card_image_of_injective _ (add_left_injective (c : ZMod p))

def shiftConst (H : Constellation) (hne : H.Nonempty) : ℤ :=
  -(H.min' hne)

lemma shiftConst_nonneg (H : Constellation) (hne : H.Nonempty) :
    ∀ h ∈ H, 0 ≤ h + shiftConst H hne := by
  intro h hh
  unfold shiftConst
  have hmin : H.min' hne ≤ h := Finset.min'_le H h hh
  omega

def natConstellation (H : Constellation) (hne : H.Nonempty) : Finset ℕ :=
  (H.image (· + shiftConst H hne)).image Int.toNat

lemma natConstellation_card (H : Constellation) (hne : H.Nonempty) :
    (natConstellation H hne).card = H.card := by
  unfold natConstellation
  have hinj_toNat : Set.InjOn Int.toNat (H.image (· + shiftConst H hne) : Finset ℤ) := by
    intro a ha b hb hab
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha hb
    obtain ⟨x, hxH, rfl⟩ := ha
    obtain ⟨y, hyH, rfl⟩ := hb
    have hxnn : 0 ≤ x + shiftConst H hne := shiftConst_nonneg H hne x hxH
    have hynn : 0 ≤ y + shiftConst H hne := shiftConst_nonneg H hne y hyH
    have hab' : ((x + shiftConst H hne).toNat : ℤ) = ((y + shiftConst H hne).toNat : ℤ) := by
      exact_mod_cast hab
    rwa [Int.toNat_of_nonneg hxnn, Int.toNat_of_nonneg hynn] at hab'
  rw [Finset.card_image_of_injOn hinj_toNat,
      Finset.card_image_of_injective _ (add_left_injective (shiftConst H hne))]

lemma natConstellation_w_eq_omega (H : Constellation) (hne : H.Nonempty) (p : ℕ) :
    RNS.w (natConstellation H hne) p = omega H p := by
  set c := shiftConst H hne with hc
  set T := natConstellation H hne with hT
  have hTcast : T.image (fun t : ℕ => (t : ℤ)) = H.image (· + c) := by
    change ((H.image (· + c)).image Int.toNat).image (fun t : ℕ => (t : ℤ)) = H.image (· + c)
    rw [Finset.image_image]
    have heq : Set.EqOn ((fun t : ℕ => (t : ℤ)) ∘ Int.toNat) id ↑(H.image (· + c)) := by
      intro z hz
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hz
      obtain ⟨h, hh, rfl⟩ := hz
      exact Int.toNat_of_nonneg (shiftConst_nonneg H hne h hh)
    rw [Finset.image_congr heq, Finset.image_id]
  have hcast_mod : ∀ a : ℕ, (a : ZMod p) = ((a % p : ℕ) : ZMod p) := by
    intro a
    conv_lhs => rw [← Nat.div_add_mod a p]
    push_cast
    rw [ZMod.natCast_self]
    ring
  have hstep : omega H p = (T.image (fun t : ℕ => (t : ZMod p))).card := by
    rw [← omega_shift H c p]
    unfold omega
    rw [← hTcast, Finset.image_image]
    have hfun : ((fun h : ℤ => (h : ZMod p)) ∘ (fun t : ℕ => (t : ℤ)))
        = (fun t : ℕ => (t : ZMod p)) := by
      funext t
      simp
    rw [hfun]
  rw [hstep]
  unfold RNS.w
  have hrw : (T.image (fun t : ℕ => (t : ZMod p)))
      = T.image (fun t : ℕ => ((t % p : ℕ) : ZMod p)) :=
    Finset.image_congr (fun t _ => hcast_mod t)
  have hcomp : (fun t : ℕ => ((t % p : ℕ) : ZMod p))
      = (fun n : ℕ => (n : ZMod p)) ∘ (fun t : ℕ => t % p) := rfl
  rw [hrw, hcomp, ← Finset.image_image]
  rcases Nat.eq_zero_or_pos p with hp0 | hppos
  · subst hp0
    exact (Finset.card_image_of_injective _ Nat.cast_injective).symm
  · have : NeZero p := ⟨hppos.ne'⟩
    have hinj : Set.InjOn (fun n : ℕ => (n : ZMod p))
        ↑(T.image (fun t : ℕ => t % p)) := by
      intro a ha b hb hab
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha hb
      obtain ⟨x, _, rfl⟩ := ha
      obtain ⟨y, _, rfl⟩ := hb
      have hax : x % p < p := Nat.mod_lt x hppos
      have hby : y % p < p := Nat.mod_lt y hppos
      have hv := congrArg ZMod.val hab
      rwa [ZMod.val_cast_of_lt hax, ZMod.val_cast_of_lt hby] at hv
    exact (Finset.card_image_of_injOn hinj).symm

/-! ### Filling Challenge's two gaps -/

noncomputable def hardyLittlewoodConstant (H : Constellation) : ℝ :=
  if hne : H.Nonempty then RNS.hardyLittlewoodConstant (natConstellation H hne) else 1

theorem hardyLittlewoodConstant_pos (H : Constellation) (hA : IsAdmissible H)
    (hk : 1 ≤ H.card) : 0 < hardyLittlewoodConstant H := by
  have hne : H.Nonempty := Finset.card_pos.mp (by omega)
  unfold hardyLittlewoodConstant
  rw [dif_pos hne]
  apply RNS.hardyLittlewoodConstantPos
  · intro p hp
    rw [natConstellation_w_eq_omega H hne p]
    exact hA p hp
  · rw [natConstellation_card]
    exact hk
