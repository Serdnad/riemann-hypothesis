module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle158
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingAlongIdealFiltration
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DFormMem
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle159
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrVB
open GlobalTheory.CompanionTheory.GrForm

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem rp_class {W : X.Opens} {P : ObjectProperty (Thick (LL q))} {d r : ℕ} {u : Fin d → ∀ T : Thick (LL q), T.B}
    {x : Idx r d → Γ(X, W)} {c c' : HU (GF q r) P r} (h : Rp (W := W) P u x c) (h' : Rp (W := W) P u x c') : c = c' := by
  obtain ⟨f, hf, rfl, hs⟩ := h
  obtain ⟨f', hf', rfl, hs'⟩ := h'
  have e : f = f' := funext fun s => Subtype.ext ((hs s).trans (hs' s).symm)
  subst e
  rfl

theorem inU_mono {W W' : X.Opens} (h : W' ≤ W) {T : Thick (LL q)} (hT : InU W' T) : InU W T :=
  hT.trans (fun _ hx => h hx)

theorem isLift_res {V W : X.Opens} (h : W ≤ V) {d : ℕ} {t : Fin d → Γ(X, V)} {u : Fin d → ∀ T : Thick (LL q), T.B}
    (hu : IsLift V t u) {t' : Fin d → Γ(X, W)} (ht : ∀ i, t' i = rs h (t i)) : IsLift W t' u := by
  intro i T hT
  rw [ht, hu i T (inU_mono h hT), ev_res h T (inU_mono h hT) hT]

theorem st_iff {Q : ObjectProperty (Thick (LL q))} {W : X.Opens} (T : Thick (LL q)) :
    St Q {W} T ↔ Q T ∧ InU W T := by
  constructor
  · rintro ⟨h, V, hV, hi⟩
    obtain rfl : V = W := hV
    exact ⟨h, hi⟩
  · rintro ⟨h, hi⟩
    exact ⟨h, W, rfl, hi⟩

theorem inU_capO {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) (T : Thick (LL q)) :
    InU (capO U i) T ↔ ∀ a, InU (U (i a)) T := by
  have e : capO U i = ⨅ a ∈ (Finset.univ : Finset (Fin n)), U (i a) := by simp [capO]
  rw [e, GlobalTheory.T.inOpen_finite_inf_iff (fun a => U (i a)) Finset.univ T]
  simp

theorem capT_eq (l s : ℕ) {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin (n + 1) → ι) :
    capT (fun α => SS q l s (U α)) i = SS q l s (capO U i) := by
  funext T
  refine propext ⟨fun h => ?_, fun h a => ?_⟩
  · exact (st_iff T).2 ⟨((st_iff T).1 (h 0)).1, (inU_capO U i T).2 fun a => ((st_iff T).1 (h a)).2⟩
  · obtain ⟨h1, h2⟩ := (st_iff T).1 h
    exact (st_iff T).2 ⟨h1, (inU_capO U i T).1 h2 a⟩

def Free (W : X.Opens) (P : ObjectProperty (Thick (LL q))) (r : ℕ) {d : ℕ} (u : Fin d → ∀ T : Thick (LL q), T.B) : Prop :=
  (∀ cl : HU (GF q r) P r, ∃ x, Rp (W := W) P u x cl) ∧ ∀ x : Idx r d → Γ(X, W), Rp (W := W) P u x 0 → x = 0

section Forms
variable {W : X.Opens} {d : ℕ} {t : Fin d → Γ(X, W)} {u : Fin d → ∀ T : Thick (LL q), T.B}
  {P : ObjectProperty (Thick (LL q))} {r : ℕ}

theorem rp_zero (hE : StExists) (hA : StAdd) (hu : IsLift W t u) (hP : ∀ T, P T → InU W T) :
    Rp (W := W) P u (0 : Idx r d → Γ(X, W)) (0 : HU (GF q r) P r) := by
  obtain ⟨c, hc⟩ := hE W t u hu P hP r 0
  have h2 := (hA W t u hu P hP r _ _ _ _ hc (hA W t u hu P hP r _ _ _ _ hc hc).2).1
  rw [add_neg_cancel, add_neg_cancel] at h2
  exact h2

theorem rp_sum (hE : StExists) (hA : StAdd) (hu : IsLift W t u) (hP : ∀ T, P T → InU W T) {κ' : Type} (S : Finset κ')
    (x : κ' → Idx r d → Γ(X, W)) (c : κ' → HU (GF q r) P r) (h : ∀ k ∈ S, Rp (W := W) P u (x k) (c k)) :
    Rp (W := W) P u (∑ k ∈ S, x k) (∑ k ∈ S, c k) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact rp_zero hE hA hu hP
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (hA W t u hu P hP r _ _ _ _ (h a (Finset.mem_insert_self a S))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))).1

theorem rp_coef (hA : StAdd) (hu : IsLift W t u) (hP : ∀ T, P T → InU W T) (hF : Free W P r u)
    {x x' : Idx r d → Γ(X, W)} {c : HU (GF q r) P r} (h : Rp (W := W) P u x c) (h' : Rp (W := W) P u x' c) : x = x' := by
  have h2 := (hA W t u hu P hP r _ _ _ _ h (hA W t u hu P hP r _ _ _ _ h' h').2).1
  rw [add_neg_cancel c] at h2
  exact add_neg_eq_zero.1 (hF.2 _ h2)

theorem exists_equiv (hE : StExists) (hA : StAdd) (hu : IsLift W t u) (hP : ∀ T, P T → InU W T) (hF : Free W P r u) :
    ∃ e : HU (GF q r) P r ≃+ (Idx r d → Γ(X, W)), ∀ cl, Rp (W := W) P u (e cl) cl := by
  choose f hf using hF.1
  choose g hg using fun x => hE W t u hu P hP r x
  exact ⟨{ toFun := f, invFun := g, left_inv := fun c => rp_class (hg _) (hf c),
           right_inv := fun x => rp_coef hA hu hP hF (hf _) (hg x),
           map_add' := fun a b => rp_coef hA hu hP hF (hf _) (hA W t u hu P hP r _ _ _ _ (hf a) (hf b)).1 }, hf⟩

end Forms

theorem free_at (hL : StLoc) {l s : ℕ} (hb : TFBase (dividedPowersBot O) l s) {V W : X.Opens} (h : W ≤ V)
    (hW : IsAffineOpen W) {d : ℕ} (c : Coord q V d) {u : Fin d → ∀ T : Thick (LL q), T.B} (hu : IsLift V c.t u)
    {r : ℕ} (hr : r < s) {P : ObjectProperty (Thick (LL q))} (hP : P = SS q l s W) : Free W P r u := by
  subst hP
  obtain ⟨c', hc'⟩ := GlobalTheory.T.coordinates_restrict_affine_open c h hW
  exact hL l s hb q c' u (isLift_res h hu hc') r hr

theorem chg (hE : StExists) (hA : StAdd) (hR : StRes) (hAct : StAct) {W W₂ : X.Opens} (h : W ≤ W₂) {da db : ℕ}
    {ta : Fin da → Γ(X, W₂)} {tb : Fin db → Γ(X, W₂)} {ua : Fin da → ∀ T : Thick (LL q), T.B}
    {ub : Fin db → ∀ T : Thick (LL q), T.B} (hua : IsLift W₂ ta ua) (hub : IsLift W₂ tb ub)
    {P P₂ : ObjectProperty (Thick (LL q))} (hPP : P ≤ P₂) (hP : ∀ T, P T → InU W T) (hP₂ : ∀ T, P₂ T → InU W₂ T) {r : ℕ}
    (A : HU (GF q r) P₂ r ≃+ (Idx r da → Γ(X, W₂))) (hA' : ∀ cl, Rp (W := W₂) P₂ ua (A cl) cl)
    (B : HU (GF q r) P₂ r ≃+ (Idx r db → Γ(X, W₂))) (hB' : ∀ cl, Rp (W := W₂) P₂ ub (B cl) cl)
    [DecidableEq (Idx r db)] (x : HU (GF q r) P r) (y : Idx r db → Γ(X, W)) (hy : Rp (W := W) P ub y x) :
    Rp (W := W) P ua (fun k => ∑ k', rs h (A (B.symm (Pi.single k' 1)) k) * y k') x := by
  have hua' : IsLift W (fun i => rs h (ta i)) ua := isLift_res h hua fun _ => rfl
  have hub' : IsLift W (fun i => rs h (tb i)) ub := isLift_res h hub fun _ => rfl
  have hb1 : ∀ k', Rp (W := W₂) P₂ ub (Pi.single k' 1) (B.symm (Pi.single k' 1)) := fun k' => by
    have := hB' (B.symm (Pi.single k' 1))
    rwa [AddEquiv.apply_symm_apply] at this
  choose m hm using fun k' => hAct W P hP r (y k')
  have hd1 : ∀ k', Rp (W := W) P ub (fun I => y k' * rs h ((Pi.single k' 1 : Idx r db → Γ(X, W₂)) I))
      (m k' ((resU (GF q r) hPP).pull r (B.symm (Pi.single k' 1)))) := fun k' =>
    hm k' _ _ hub' _ _ (hR W₂ W h tb ub hub P₂ P hPP hP₂ hP r _ _ (hb1 k'))
  have hd2 : ∀ k', Rp (W := W) P ua (fun I => y k' * rs h (A (B.symm (Pi.single k' 1)) I))
      (m k' ((resU (GF q r) hPP).pull r (B.symm (Pi.single k' 1)))) := fun k' =>
    hm k' _ _ hua' _ _ (hR W₂ W h ta ua hua P₂ P hPP hP₂ hP r _ _ (hA' _))
  have s1 := rp_sum hE hA hub' hP Finset.univ _ _ fun k' _ => hd1 k'
  have s2 := rp_sum hE hA hua' hP Finset.univ _ _ fun k' _ => hd2 k'
  have e1 : (∑ k', fun I => y k' * rs h ((Pi.single k' 1 : Idx r db → Γ(X, W₂)) I)) = y := by
    funext I
    rw [Finset.sum_apply, Finset.sum_eq_single I]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne (Ne.symm hb)]
    · simp
  rw [e1] at s1
  rw [rp_class s1 hy] at s2
  convert s2 using 1
  funext k
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem capO_pair {ι : Type} (U : ι → X.Opens) (α β : ι) : capO U ![α, β] = U α ⊓ U β := by
  refine le_antisymm (le_inf (capO_le U _ 0) (capO_le U _ 1)) (le_iInf fun a => ?_)
  fin_cases a
  · exact inf_le_left
  · exact inf_le_right

theorem capT_inU (l s : ℕ) {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) (T : Thick (LL q))
    (h : capT (fun α => SS q l s (U α)) i T) : InU (capO U i) T :=
  (inU_capO U i T).2 fun a => ((st_iff T).1 (h a)).2

theorem ss_inU (l s : ℕ) (W : X.Opens) (T : Thick (LL q)) (h : SS q l s W T) : InU W T := ((st_iff T).1 h).2

section Main
variable {ι : Type} (U : ι → X.Opens) (d : ι → ℕ) (c : ∀ α, Coord q (U α) (d α))

def uu (α : ι) : Fin (d α) → ∀ T : Thick (LL q), T.B := fun k T => lft (U α) T ((c α).t k)

theorem uu_lift (α : ι) : IsLift (U α) (c α).t (uu U d c α) := fun k T h => lft_spec T h _

theorem uu_res (α : ι) {W : X.Opens} (h : W ≤ U α) : IsLift W (fun k => rs h ((c α).t k)) (uu U d c α) :=
  isLift_res h (uu_lift U d c α) fun _ => rfl

end Main

theorem main : StExists → StAdd → StSmul → StRes → StAct → StLoc → StVB := by
  classical
  intro hE hA hS hR hAct hL O _ l s hb X q ι _ U d c ha r hr
  have hPi : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (T : Thick (LL q)), capT (fun α => SS q l s (U α)) i T → InU (capO U i) T :=
    fun i T h => capT_inU l s U i T h
  have hFi : ∀ (n : ℕ) (a : Fin (n + 1)) (i : Fin (n + 1) → ι),
      Free (capO U i) (capT (fun α => SS q l s (U α)) i) r (uu U d c (i a)) := fun n a i =>
    free_at hL hb (capO_le U i a) (ha n i) (c (i a)) (uu_lift U d c (i a)) hr (capT_eq l s U i)
  choose E hEr using fun (n : ℕ) (a : Fin (n + 1)) (i : Fin (n + 1) → ι) =>
    exists_equiv hE hA (uu_res U d c (i a) (capO_le U i a)) (hPi i) (hFi n a i)
  have aff2 : ∀ α β, IsAffineOpen (U α ⊓ U β) := fun α β => by
    rw [← capO_pair]
    exact ha 1 _
  choose A hAr using fun α β => exists_equiv (P := SS q l s (U α ⊓ U β)) (r := r) hE hA (uu_res U d c α inf_le_left)
    (ss_inU l s (U α ⊓ U β)) (free_at hL hb inf_le_left (aff2 α β) (c α) (uu_lift U d c α) hr rfl)
  choose B hBr using fun α β => exists_equiv (P := SS q l s (U α ⊓ U β)) (r := r) hE hA (uu_res U d c β inf_le_right)
    (ss_inU l s (U α ⊓ U β)) (free_at hL hb inf_le_right (aff2 α β) (c β) (uu_lift U d c β) hr rfl)
  refine ⟨{ κ := fun α => Idx r (d α)
            fin := fun _ => inferInstance
            g := fun α β k k' => A α β ((B α β).symm (Pi.single k' 1)) k
            e := fun n a => AddEquiv.piCongrRight fun i => E n a i
            e_smul := ?_
            e_δ := ?_
            e_chg := ?_ }⟩
  · intro n a z x i k
    have := rp_coef hA (uu_res U d c (i a) (capO_le U i a)) (hPi i) (hFi n a i) (hEr n a i (z • x i))
      (hS _ _ _ (uu_res U d c (i a) (capO_le U i a)) _ (hPi i) r _ _ z (hEr n a i (x i)))
    exact congrFun this k
  · intro n a b x i k
    have := rp_coef hA (uu_res U d c (i (b.succAbove a)) (capO_le U i (b.succAbove a))) (hPi i) (hFi (n + 1) (b.succAbove a) i)
      (hEr (n + 1) (b.succAbove a) i _)
      (hR _ _ (capO_comp U i b.succAbove) _ _ (uu_res U d c (i (b.succAbove a)) (capO_le U (i ∘ b.succAbove) a))
        _ (capT (fun α => SS q l s (U α)) i) (fun _ h _ => h _) (hPi _) (hPi i) r _ _ (hEr n a (i ∘ b.succAbove) (x (i ∘ b.succAbove))))
    exact congrFun this k
  · intro n a b x i k
    have hle : capO U i ≤ U (i a) ⊓ U (i b) := le_inf (capO_le U i a) (capO_le U i b)
    have hPP : capT (fun α => SS q l s (U α)) i ≤ SS q l s (U (i a) ⊓ U (i b)) := fun T h =>
      (st_iff T).2 ⟨((st_iff T).1 (h a)).1, inU_mono hle (hPi i T h)⟩
    have := rp_coef hA (uu_res U d c (i a) (capO_le U i a)) (hPi i) (hFi n a i) (hEr n a i (x i))
      (chg hE hA hR hAct hle (uu_res U d c (i a) inf_le_left) (uu_res U d c (i b) inf_le_right) hPP (hPi i)
        (ss_inU l s _) (A (i a) (i b)) (hAr _ _) (B (i a) (i b)) (hBr _ _) (x i) _ (hEr n b i (x i)))
    exact congrFun this k

end GlobalTheory.CompanionTheory.GrVB
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)
open GlobalTheory.CompanionTheory.CocProd (tele sa_val)
open GlobalTheory.CompanionTheory.TowerEnd (Q dQ val Vals cl d_cl dQ_apply)

noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm.Coc

theorem alt_sum {B : Type*} [CommRing B] {j : ℕ} (w : Fin j → Fin (j + 2) → B) :
    ∑ i : Fin (j + 2), (-1 : B) ^ (i : ℕ) *
      ∏ k : Fin j, (w k (i.succAbove k.succ) - w k (i.succAbove k.castSucc)) = 0 := by
  classical
  set u : Fin j → B := fun k => w k k.succ.castSucc - w k k.castSucc.castSucc with hu
  set v : Fin j → B := fun k => w k k.succ.succ - w k k.succ.castSucc with hv
  set P : ℕ → B := fun n => ∏ k : Fin j, if (k : ℕ) < n then u k else v k with hP
  set T : Fin (j + 2) → B := fun i =>
    ∏ k : Fin j, (w k (i.succAbove k.succ) - w k (i.succAbove k.castSucc)) with hT
  have cg : ∀ (k : Fin j) {p q p' q' : Fin (j + 2)}, (p : ℕ) = p' → (q : ℕ) = q' →
      w k p - w k q = w k p' - w k q' := by
    intro k p q p' q' h h'
    rw [Fin.ext h, Fin.ext h']
  have hT0 : T (Fin.castSucc 0) = P 0 := by
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [Nat.not_lt_zero, if_false]
    refine cg k ?_ ?_ <;> simp only [sa_val, Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Fin.val_last] <;> split_ifs <;> omega
  have hTl : T (Fin.last (j + 1)) = P j := by
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [k.2, if_true]
    refine cg k ?_ ?_ <;> simp only [sa_val, Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Fin.val_last] <;> split_ifs <;> omega
  have hTi : ∀ i : Fin j, T i.succ.castSucc = P (i + 1) + P i := by
    intro i
    have hPa : P (i + 1) = u i * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i + 1 then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => if (k : ℕ) < i + 1 then u k else v k) (Finset.mem_univ i)
      simp only [Nat.lt_add_one, if_true] at this
      exact this.symm
    have hPb : P i = v i * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => if (k : ℕ) < i then u k else v k) (Finset.mem_univ i)
      simp only [lt_irrefl, if_false] at this
      exact this.symm
    have hTa : T i.succ.castSucc = (u i + v i) * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => w k (i.succ.castSucc.succAbove k.succ) -
        w k (i.succ.castSucc.succAbove k.castSucc)) (Finset.mem_univ i)
      refine this.symm.trans ?_
      congr 1
      · have e : u i + v i = w i i.succ.succ - w i i.castSucc.castSucc := by
          rw [hu, hv]; ring
        rw [e]
        refine cg i ?_ ?_ <;> simp only [sa_val, Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Fin.val_last] <;> split_ifs <;> omega
      · refine Finset.prod_congr rfl fun k hk => ?_
        have hki : (k : ℕ) ≠ i := fun h => Finset.ne_of_mem_erase hk (Fin.ext h)
        split_ifs with h
        · refine cg k ?_ ?_ <;> simp only [sa_val, Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Fin.val_last] <;> split_ifs <;> omega
        · refine cg k ?_ ?_ <;> simp only [sa_val, Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Fin.val_last] <;> split_ifs <;> omega
    have hE : ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i + 1 then u k else v k) =
        ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      refine Finset.prod_congr rfl fun k hk => ?_
      have hki : (k : ℕ) ≠ i := fun h => Finset.ne_of_mem_erase hk (Fin.ext h)
      have : (k : ℕ) < i + 1 ↔ (k : ℕ) < i := by omega
      simp only [this]
    rw [hTa, hPa, hPb, hE]
    ring
  change ∑ i : Fin (j + 2), (-1 : B) ^ (i : ℕ) * T i = 0
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  have hint : ∑ i : Fin j, (-1 : B) ^ ((i.succ.castSucc : Fin (j + 2)) : ℕ) * T i.succ.castSucc =
      ∑ m ∈ Finset.range j, (-1 : B) ^ (m + 1) * (P (m + 1) + P m) := by
    rw [← Fin.sum_univ_eq_sum_range (fun m => (-1 : B) ^ (m + 1) * (P (m + 1) + P m)) j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hTi]
    simp only [Fin.val_castSucc, Fin.val_succ]
  rw [hint, hT0, hTl]
  simp only [Fin.val_castSucc, Fin.val_zero, Fin.val_last, pow_zero]
  linear_combination tele P j

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

def vt (c : ∀ T : C, Φ.A.obj T) {n : ℕ} (s : ComposableArrows C n) (p : Fin (n + 1)) :
    Φ.A.obj (s.obj (Fin.last n)) :=
  (Φ.A.map (s.map (homOfLE (Fin.le_last p)))).hom (c (s.obj p))

theorem vt_last (c : ∀ T : C, Φ.A.obj T) {n : ℕ} (s : ComposableArrows C n) (p : Fin (n + 1))
    (hp : p = Fin.last n) : vt c s p = c (s.obj (Fin.last n)) := by
  subst hp
  have : (homOfLE (Fin.le_last (Fin.last n)) : Fin.last n ⟶ Fin.last n) = 𝟙 _ := Subsingleton.elim _ _
  unfold vt
  rw [this, s.map_id]
  simp

theorem face_vt (c : ∀ T : C, Φ.A.obj T) {j : ℕ} (s : ComposableArrows C (j + 1)) (i : Fin (j + 2)) :
    (Φ.A.map (toLast i s)).hom (c ((face i s).obj (Fin.last j))) = vt c s (i.succAbove (Fin.last j)) := rfl

theorem face_wz {d j : ℕ} (u : Fin d → ∀ T : C, Φ.A.obj T) (I : Fin j → Fin d)
    (s : ComposableArrows C (j + 1)) (i : Fin (j + 2)) :
    (Φ.A.map (toLast i s)).hom (wz u I (face i s)) =
      ∏ k : Fin j, (vt (u (I k)) s (i.succAbove k.succ) - vt (u (I k)) s (i.succAbove k.castSucc)) := by
  have map_map {X Y Z : C} (g : X ⟶ Y) (f : Y ⟶ Z) (y : Φ.A.obj X) :
      (Φ.A.map f).hom ((Φ.A.map g).hom y) = (Φ.A.map (g ≫ f)).hom y := by
    simp
  unfold wz
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [map_sub]
  rw [map_map]
  have e : (face i s).map (homOfLE (Fin.le_last k.succ)) ≫ toLast i s =
      s.map (homOfLE (Fin.le_last (i.succAbove k.succ))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  rw [e, map_map, e, map_map]
  have e2 : (face i s).map (homOfLE (Fin.castSucc_lt_succ (i := k)).le) ≫
      s.map (homOfLE (Fin.le_last (i.succAbove k.succ))) =
      s.map (homOfLE (Fin.le_last (i.succAbove k.castSucc))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  rw [e2]
  rfl

theorem d_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d j : ℕ} (u : Fin d → ∀ T : C, Φ.A.obj T)
    (hu : ∀ i {T T' : C} (φ : T ⟶ T'), u i T' - (Φ.A.map φ).hom (u i T) ∈ Φ.J.S T')
    (y : ∀ T : C, Φ.A.obj T) (hy : ∀ {T T' : C} (φ : T ⟶ T'), y T' - (Φ.A.map φ).hom (y T) ∈ Φ.J.S T')
    (I : Fin j → Fin d) (s : ComposableArrows C (j + 1)) :
    ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom
      (wz u I (face i s) * y ((face i s).obj (Fin.last j))) ∈ (Fil ((j : ℤ) + 1)).S _ := by
  set Y := y (s.obj (Fin.last (j + 1))) with hY
  set T : Fin (j + 2) → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun i =>
    ∏ k : Fin j, (vt (u (I k)) s (i.succAbove k.succ) - vt (u (I k)) s (i.succAbove k.castSucc)) with hT
  set V : Fin (j + 2) → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun i =>
    vt y s (i.succAbove (Fin.last j)) with hV
  have hVY : ∀ i : Fin (j + 1), V i.castSucc = Y := by
    intro i
    refine vt_last y s _ (Fin.ext ?_)
    have := i.2
    rw [sa_val]
    simp only [Fin.val_last, Fin.val_castSucc]
    split_ifs <;> omega
  have hsum : ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom
      (wz u I (face i s) * y ((face i s).obj (Fin.last j))) =
      (-1) ^ j * (T (Fin.last (j + 1)) * (Y - V (Fin.last (j + 1)))) := by
    have hterm : ∀ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom
        (wz u I (face i s) * y ((face i s).obj (Fin.last j))) = (-1) ^ (i : ℕ) * (T i * V i) := by
      intro i
      rw [map_mul, face_wz, face_vt, zsmul_eq_mul]
      push_cast
      rfl
    have h0 := alt_sum (B := Φ.A.obj (s.obj (Fin.last (j + 1)))) (j := j) (fun k p => vt (u (I k)) s p)
    change ∑ i : Fin (j + 2), (-1) ^ (i : ℕ) * T i = 0 at h0
    rw [Fin.sum_univ_castSucc] at h0
    rw [Finset.sum_congr rfl fun i _ => hterm i, Fin.sum_univ_castSucc]
    have h1 : ∑ i : Fin (j + 1), (-1) ^ ((i.castSucc : Fin (j + 2)) : ℕ) * (T i.castSucc * V i.castSucc) =
        (∑ i : Fin (j + 1), (-1) ^ ((i.castSucc : Fin (j + 2)) : ℕ) * T i.castSucc) * Y := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hVY]
      ring
    rw [h1]
    simp only [Fin.val_last] at h0 ⊢
    linear_combination Y * h0
  rw [hsum]
  refine Ideal.mul_mem_left _ _ ?_
  have hA : T (Fin.last (j + 1)) ∈ (Fil (j : ℤ)).S _ := by
    have := (Fil (j : ℤ)).map_mem (toLast (Fin.last (j + 1)) s) (wz_mem hF u hu I (face (Fin.last (j + 1)) s))
    rwa [face_wz] at this
  have hB : Y - V (Fin.last (j + 1)) ∈ (Fil ((1 : ℕ) : ℤ)).S _ := by
    have e : (((1 : ℕ) : ℤ)) = 1 := rfl
    rw [e, hF.one]
    have h := hy (s.map (homOfLE (show (Fin.last j).castSucc ≤ Fin.last (j + 1) from Fin.le_last _)))
    have e2 : V (Fin.last (j + 1)) = (Φ.A.map (s.map (homOfLE (show (Fin.last j).castSucc ≤ Fin.last (j + 1) from Fin.le_last _)))).hom
        (y (s.obj (Fin.last j).castSucc)) := by
      have : (Fin.last (j + 1)).succAbove (Fin.last j) = (Fin.last j).castSucc := Fin.succAbove_last_apply _
      simp only [hV, vt]
      rw [this]
    rw [e2]
    exact h
  have h := hF.mul j 1 _ hA hB
  have e : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
  rwa [e] at h

end GlobalTheory.CompanionTheory.GrForm.Coc


open GlobalTheory.CompanionTheory.GrForm.Coc in
theorem GlobalTheory.CompanionTheory.GrForm.stCocycle : GlobalTheory.CompanionTheory.GrForm.StCocycle := by
  intro R _ C _ Φ Fil hF d j u hu y hy I
  let z : Q Φ.A j := fun s => (wz u I s * y (s.obj (Fin.last j)) : Φ.A.obj (s.obj (Fin.last j)))
  have hz : Vals (Fil j) z := fun s => Ideal.mul_mem_right _ _ (wz_mem hF u hu I s)
  refine ⟨cl (Fil j) (Fil ((j : ℤ) + 1)) z hz, ?_, fun s => rfl⟩
  rw [d_cl]
  funext s
  apply Subtype.ext
  change Ideal.Quotient.mk _ (val (dQ Φ.A j z) s) = 0
  rw [dQ_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (d_mem hF u hu y hy I s)
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.chart_property_propagates : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ) (k : Fin m) ⦃T T' : Thick (smFun X q)⦄,
    (T ⟶ T') → wK q i y s k T → (∃ β, wK q i y s β T') → wK q i y s k T' := by
  first | exact @GlobalTheory.CompanionTheory.ConeSite.wK_rel | exact GlobalTheory.CompanionTheory.ConeSite.wK_rel | (intros; apply GlobalTheory.CompanionTheory.ConeSite.wK_rel <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.homogeneous_ratio_cocycle : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N m e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (a b c : Fin m) (W : X.Opens)
    (ha : W ≤ uy i y a) (hb : W ≤ uy i y b) (hc : W ≤ uy i y c),
    (i.appLE _ W hb).hom (yQ y hy a b) * (i.appLE _ W hc).hom (yQ y hy b c) = (i.appLE _ W hc).hom (yQ y hy a c) ∧
    (i.appLE _ W ha).hom (yQ y hy a a) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.ConeYq.yQ_mul_yQ | exact GlobalTheory.CompanionTheory.ConeYq.yQ_mul_yQ | (intros; apply GlobalTheory.CompanionTheory.ConeYq.yQ_mul_yQ <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.torus_coordinate_isUnit : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens} (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)), ∀ k : Fin d, IsUnit (tV i y hy V hV k) := by
  first | exact @GlobalTheory.CompanionTheory.GeoUnit.tV_isUnit | exact GlobalTheory.CompanionTheory.GeoUnit.tV_isUnit | (intros; apply GlobalTheory.CompanionTheory.GeoUnit.tV_isUnit <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.truncated_log_multiplicative : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ), pdP δ s = ⊥ → (∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) → ∀ {x y : B}, x ∈ J → y ∈ J → plogK δ s ((1 + x) * (1 + y) - 1) = plogK δ s x + plogK δ s y := by
  first | exact @GlobalTheory.CompanionTheory.PlogMul.plogK_mul | exact GlobalTheory.CompanionTheory.PlogMul.plogK_mul | (intros; apply GlobalTheory.CompanionTheory.PlogMul.plogK_mul <;> assumption)
end
