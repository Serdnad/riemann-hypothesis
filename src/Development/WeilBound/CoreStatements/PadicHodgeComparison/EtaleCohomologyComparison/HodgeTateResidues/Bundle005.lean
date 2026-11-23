module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInJAlt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle002
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftPOfBounds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle183
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT

open Pb Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem dividedPowerFiltration_one {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) : pdP δ 1 = J := by
  refine le_antisymm (Ideal.span_le.2 ?_) fun z hz => by simpa using pow_mem_pdP δ hz 1
  rintro _ ⟨L, hL, hr, rfl⟩
  induction L with
  | nil => simp at hr
  | cons q L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons] at hr ⊢
    rcases Nat.eq_zero_or_pos q.1 with h | h
    · exact J.mul_mem_left _ (ih (fun q' hq' => hL q' (List.mem_cons_of_mem _ hq')) (by omega))
    · exact J.mul_mem_right _ (δ.dpow_mem h.ne' (hL q List.mem_cons_self))

structure Br (R : Per l K) (Y : CB l K) (e : Y.Λ →+* R.A) (θP : R.P →+* ℂ_[l]) (sΛ : K.fixingSubgroup → Y.Λ →+* Y.Λ)
    (sn : K.fixingSubgroup → ∀ n, Y.R n →+* Y.R n) (sC : K.fixingSubgroup → ℂ_[l] →+* ℂ_[l]) (c : K.fixingSubgroup → ℂ_[l]) : Prop where
  et : e Y.t = R.t
  t_ne : R.tB ≠ 0
  θ_i : ∀ x, ∃ y : R.P, (y : R.B) = R.i (e x) ∧ θP y = Y.θ x
  θ_o : ∀ k : K, ∃ y : R.P, (y : R.B) = R.o k ∧ θP y = kC K k
  ker : ∀ x : R.P, θP x = 0 ↔ ∃ y : R.P, (x : R.B) = R.tB * y
  θ_σ : ∀ (g : K.fixingSubgroup) (x : R.P), ∃ y : R.P, R.σ g x = y ∧ θP y = sC g (θP x)
  galois_t_transform : ∀ g : K.fixingSubgroup, ∃ u : R.P, R.σ g R.tB = u * R.tB ∧ θP u = c g
  eσ : ∀ g x, e (sΛ g x) = R.σA g (e x)
  cris : ∀ g n x, sn g n (Y.c n x) = Y.c n (sΛ g x)

variable {R : Per l K} {Y : CB l K} {e : Y.Λ →+* R.A} {θP : R.P →+* ℂ_[l]} {sΛ : K.fixingSubgroup → Y.Λ →+* Y.Λ}
  {sn : K.fixingSubgroup → ∀ n, Y.R n →+* Y.R n} {sC : K.fixingSubgroup → ℂ_[l] →+* ℂ_[l]} {c : K.fixingSubgroup → ℂ_[l]}
  (hb : Br R Y e θP sΛ sn sC c) {m : ℕ} {L : Lev R m} (hL : L.Good)

include hb hL

theorem Br.θ_ex : ∃ θ : L.B →+* ℂ_[l], ∀ x, θ (L.toB x) = θP x := by
  refine ⟨(L.toB.liftOfSurjective hL.toB_surj) ⟨θP, fun x hx => ?_⟩, fun x => RingHom.liftOfRightInverse_comp_apply _ _ _ _ _⟩
  obtain ⟨y, hy⟩ := (hL.toB_ker x).1 hx
  obtain ⟨t, ht, -⟩ := hb.θ_i Y.t
  rw [hb.et] at ht
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hL.pos
  refine (hb.ker x).2 ⟨t ^ k * y, ?_⟩
  rw [hy, hk, pow_add, pow_one, Subring.coe_mul, SubmonoidClass.coe_pow, ht, mul_assoc]
  rfl

theorem Br.t_ex : ∃ t : R.P, (t : R.B) = R.tB ∧ L.ι (L.lam (e Y.t)) = L.toB t ∧ L.IB = Ideal.span {L.toB t} := by
  obtain ⟨t, ht, -⟩ := hb.θ_i Y.t
  refine ⟨t, by rw [ht, hb.et]; rfl, hL.ι_lam _ t ht, ?_⟩
  rw [← dividedPowerFiltration_one L.γB, hL.pdP_B 1 t (by rw [ht, hb.et]; rfl), pow_one]

def Br.θ : L.B →+* ℂ_[l] := (hb.θ_ex hL).choose

theorem Br.θ_toB (x : R.P) : hb.θ hL (L.toB x) = θP x := (hb.θ_ex hL).choose_spec x

theorem Br.ker_θ : RingHom.ker (hb.θ hL) = L.IB := by
  obtain ⟨t, ht, -, hI⟩ := hb.t_ex hL
  ext b
  obtain ⟨x, rfl⟩ := hL.toB_surj b
  rw [RingHom.mem_ker, hb.θ_toB, hI, Ideal.mem_span_singleton']
  constructor
  · intro h
    obtain ⟨y, hy⟩ := (hb.ker x).1 h
    refine ⟨L.toB y, ?_⟩
    rw [← map_mul]
    exact congrArg L.toB (Subtype.ext (by rw [hy, Subring.coe_mul, ht, mul_comm]))
  · rintro ⟨a, ha⟩
    have h0 : θP t = 0 := (hb.ker t).2 ⟨1, by rw [ht]; simp⟩
    rw [← hb.θ_toB hL, ← ha, map_mul, hb.θ_toB, h0, mul_zero]

theorem Br.gr (i : ℕ) (hi : i < m) (x : L.B)
    (h : x * L.ι (L.lam (e Y.t)) ^ i ∈ Ideal.span {L.ι (L.lam (e Y.t)) ^ (i + 1)}) : x ∈ L.IB := by
  obtain ⟨t, ht, h1, hI⟩ := hb.t_ex hL
  rw [h1] at h
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h
  obtain ⟨x, rfl⟩ := hL.toB_surj x
  obtain ⟨a, rfl⟩ := hL.toB_surj a
  have h2 : L.toB (x * t ^ i - a * t ^ (i + 1)) = 0 := by
    rw [map_sub, map_mul, map_mul, map_pow, map_pow, ha, sub_self]
  obtain ⟨y, hy⟩ := (hL.toB_ker _).1 h2
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hi
  have h3 : x = (a + t ^ k * y) * t := by
    refine Subtype.ext (mul_right_cancel₀ (pow_ne_zero i hb.t_ne) ?_)
    push_cast at hy ⊢
    rw [ht] at hy ⊢
    linear_combination hy
  rw [hI, h3, map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

def Br.lv (hd : ∀ n, ∃ d : RedIn (O := OK l K) (Y.γ n) (Y.κ n) L.γ l n, ∀ x, d.ρ (Y.c n x) = Ideal.Quotient.mk _ (L.lam (e x))) :
    Lv Y m where
  B := L.B
  IB := L.IB
  γB := L.γB
  θ := hb.θ hL
  A := L.A
  I := L.I
  γ := L.γ
  ι := L.ι
  lam := L.lam.comp e
  d n := (hd n).choose
  d_lam n := (hd n).choose_spec
  lat := hL.lat m le_rfl
  ι_dp := hL.ι_dp
  ι_O := hL.ι_O
  t_mem := by
    obtain ⟨t, -, h1, hI⟩ := hb.t_ex hL
    rw [hL.ι_I, Ideal.mem_comap, RingHom.comp_apply, h1, hI]
    exact Ideal.mem_span_singleton_self _
  θ_K k := by
    obtain ⟨y, h1, h2⟩ := hb.θ_o k
    rw [← hL.toB_K k y h1, hb.θ_toB, h2]
  θ_lam x := by
    obtain ⟨y, h1, h2⟩ := hb.θ_i x
    rw [RingHom.comp_apply, hL.ι_lam _ y h1, hb.θ_toB, h2]
  ker_θ := hb.ker_θ hL
  pdB r := by
    obtain ⟨t, ht, h1, -⟩ := hb.t_ex hL
    rw [RingHom.comp_apply, h1, hL.pdP_B r t ht]
  nil := by
    obtain ⟨t, ht, h1, -⟩ := hb.t_ex hL
    rw [RingHom.comp_apply, h1, ← map_pow]
    exact (hL.toB_ker _).2 ⟨1, by simp [ht]⟩
  gr := hb.gr hL

theorem Br.gal (hd) (g : K.fixingSubgroup) : Nonempty (LHom (hb.lv hL hd) (hb.lv hL hd) (sΛ g) (sn g) (sC g) (c g)) := by
  obtain ⟨u, hu, hc⟩ := hb.galois_t_transform g
  obtain ⟨t, ht, h1, -⟩ := hb.t_ex hL
  exact ⟨{
    le := le_rfl
    sA := L.σA g
    sB := L.σB g
    dpA := hL.σ_dp g
    dpB := hL.σB_dp g
    oA := hL.σ_O g
    oB := hL.σB_K g
    ι := fun a => (hL.σ_ι g a).symm
    lam := fun x => (hL.σ_lam g (e x)).trans (congrArg L.lam (hb.eσ g x).symm)
    cris := hb.cris g
    θ := fun b => by
      obtain ⟨x, rfl⟩ := hL.toB_surj b
      obtain ⟨y, h2, h3⟩ := hb.θ_σ g x
      change hb.θ hL (L.σB g (L.toB x)) = sC g (hb.θ hL (L.toB x))
      rw [hL.σB_toB g x y h2, hb.θ_toB, hb.θ_toB, h3]
    cB := L.toB u
    t := by
      change L.σB g (L.ι (L.lam (e Y.t))) = L.toB u * L.ι (L.lam (e Y.t))
      rw [h1, ← map_mul]
      exact hL.σB_toB g t (u * t) (by rw [Subring.coe_mul, ht, hu])
    θc := (hb.θ_toB hL u).trans hc }⟩

omit hL in
theorem Br.sys (S : LevSys R) (hS : S.Good)
    (hd : ∀ m n, ∃ d : RedIn (O := OK l K) (Y.γ n) (Y.κ n) (S.L m).γ l n,
      ∀ x, d.ρ (Y.c n x) = Ideal.Quotient.mk _ ((S.L m).lam (e x))) : Nonempty (LvSys Y sΛ sn sC c) :=
  ⟨{ L := fun m => hb.lv (hS.lev m) (hd m)
     dn := fun m =>
      { le := Nat.le_succ _
        sA := S.dA m
        sB := S.dB m
        dpA := hS.ddp m
        dpB := hS.ddpB m
        oA := hS.dO m
        oB := hS.dK m
        ι := hS.dι m
        lam := fun x => hS.dlam m (e x)
        cris := fun _ _ => rfl
        θ := fun b => by
          obtain ⟨x, rfl⟩ := (hS.lev (m + 1)).toB_surj b
          change hb.θ (hS.lev m) (S.dB m ((S.L (m + 1)).toB x)) = hb.θ (hS.lev (m + 1)) ((S.L (m + 1)).toB x)
          rw [hS.dB_toB, hb.θ_toB, hb.θ_toB]
        cB := 1
        t := by
          change S.dB m ((S.L (m + 1)).ι ((S.L (m + 1)).lam (e Y.t))) = 1 * (S.L m).ι ((S.L m).lam (e Y.t))
          rw [hS.dι, hS.dlam, one_mul]
        θc := map_one _ }
     gal := fun m g => (hb.gal (hS.lev m) (hd m) g).some }⟩

end CrystallineSemistableComparison.HT
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT.RhoA

open Pb GlobalTheory.CompanionTheory.LiftLat

section Gr
variable {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L))

theorem pow_tf (c : b.R) (r : ℤ)
    (hT : ∀ (T : Q.FullSubcategory) (x : (sP Q).A.obj T), c • x ∈ (sFil Q r).S T → x ∈ (sFil Q r).S T) (n : ℕ)
    (T : Q.FullSubcategory) (x : (sP Q).A.obj T) (h : c ^ n • x ∈ (sFil Q r).S T) : x ∈ (sFil Q r).S T := by
  induction n generalizing x with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ, mul_smul] at h
    exact hT T x (ih _ h)

theorem gr_part (c : b.R) (r : ℕ)
    (hT : ∀ (r : ℤ) (T : Q.FullSubcategory) (x : (sP Q).A.obj T), c • x ∈ (sFil Q r).S T → x ∈ (sFil Q r).S T) (j k : ℕ)
    (h1 : ∀ (x : HG Q r (j + 1)) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0)
    (h2 : ∀ x : HG Q r j, (∀ n : ℕ, ∃ y, x = c ^ n • y) → c ^ k • x = 0)
    (h3 : ∀ x : ℕ → HG Q r j, (∀ n, ∃ y, x (n + 1) - x n = c ^ n • y) → ∃ z : HG Q r j, ∀ n, ∃ y, z - c ^ k • x n = c ^ n • y) :
    (∀ x : ∀ n, HGm Q (c ^ n) r j, (∀ n, trG Q c n r j (x (n + 1)) = x n) →
      ∃ z : HG Q r j, ∀ n, redG' Q (c ^ n) r j z = c ^ (2 * k) • x n) ∧
    ∀ z : HG Q r j, (∀ n, redG' Q (c ^ n) r j z = 0) → c ^ k • z = 0 := by
  have hle : ∀ T : Q.FullSubcategory, (sFil Q ((r : ℤ) + 1)).S T ≤ (sFil Q r).S T := fun T => T.obj.pdPow_anti (Nat.le_succ r)
  let red := fun n : ℕ => sqLe (a := sFil Q r) (b := sFil Q ((r : ℤ) + 1)) (a' := stdI Q (some (r : ℤ)) (c ^ n))
    (b' := stdI Q (some ((r : ℤ) + 1)) (c ^ n)) (fun _ => le_sup_left) fun _ => le_sup_left
  let tr := fun n : ℕ => sqLe (stdI_le Q (some (r : ℤ)) c n) (stdI_le Q (some ((r : ℤ) + 1)) c n)
  refine gen (G := fun n => sq (stdI Q (some (r : ℤ)) (c ^ n)) (stdI Q (some ((r : ℤ) + 1)) (c ^ n))) c red tr
    (fun n T => (red n).τ T) (fun n T => (tr n).τ T) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) ?_ ?_ ?_ ?_ j k h1 h2 h3
  · intro n T x
    obtain ⟨y, hy, rfl⟩ := sq_surj _ _ x
    rfl
  · intro n T y
    obtain ⟨y, hy, rfl⟩ := sq_surj _ _ y
    obtain ⟨u, hu⟩ := (mem_some Q r _ T y).1 hy
    refine ⟨sqMk _ _ _ hu, (sq_eq _ _ (Ideal.mem_sup_left hu) hy).2 ((mem_some Q _ _ T _).2 ⟨-u, ?_⟩)⟩
    rw [smul_neg, show y - c ^ n • u - y - -(c ^ n • u) = 0 by abel]
    exact zero_mem _
  · intro n T x
    obtain ⟨w, hw, rfl⟩ := sq_surj _ _ x
    have e1 : (red n).τ T (sqMk _ _ w hw) = 0 ↔ w ∈ (stdI Q (some ((r : ℤ) + 1)) (c ^ n)).S T :=
      sqMk_eq_zero (stdI Q (some (r : ℤ)) (c ^ n)) _ w (Ideal.mem_sup_left hw)
    refine e1.trans ((mem_some Q _ _ T w).trans ⟨?_, ?_⟩)
    · rintro ⟨y, hy⟩
      have hy' : y ∈ (sFil Q r).S T := pow_tf Q c r (hT r) n T y (by
        have := sub_mem hw (hle T hy)
        rwa [sub_sub_cancel] at this)
      exact ⟨sqMk _ _ y hy', (sq_eq _ _ hw (Submodule.smul_of_tower_mem _ _ hy')).2 hy⟩
    · rintro ⟨y, h⟩
      obtain ⟨y, hy, rfl⟩ := sq_surj _ _ y
      exact ⟨y, (sq_eq _ _ hw (Submodule.smul_of_tower_mem _ _ hy)).1 h⟩
  · intro T x hx
    obtain ⟨w, hw, rfl⟩ := sq_surj _ _ x
    have e2 := (sqMk_eq_zero _ _ (c • w) (Submodule.smul_of_tower_mem _ _ hw)).1 hx
    exact (sqMk_eq_zero _ _ w hw).2 (hT _ T w e2)

end Gr

theorem lift_gr (hA : AfgA) {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] {I : Ideal A}
    (γ : DividedPowers I) (l m : ℕ) (hdv : ∀ a : O, a ≠ 0 → ∃ k : ℕ, a ∣ (l : O) ^ k) (hO : TFBase (dividedPowersBot O) l m)
    (hL : LatBase γ l m) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (U : Cov q) (r : ℕ) (hr : r < m) (j : ℕ) :
    ∃ k : ℕ, (∀ x : ∀ n, HGm (TS γ q l m {⊤}) ((l : A) ^ n) r j, (∀ n, trG (TS γ q l m {⊤}) (l : A) n r j (x (n + 1)) = x n) →
      ∃ z : HG (TS γ q l m {⊤}) r j, ∀ n, redG' (TS γ q l m {⊤}) ((l : A) ^ n) r j z = (l : A) ^ (2 * k) • x n) ∧
    ∀ z : HG (TS γ q l m {⊤}) r j, (∀ n, redG' (TS γ q l m {⊤}) ((l : A) ^ n) r j z = 0) → (l : A) ^ k • z = 0 := by
  have hf := fun j => hA γ l m m hdv hO hL le_rfl q U {⊤} sSup_singleton r ((r : ℤ) + 1) (by omega) (by omega) j
  obtain ⟨k, a, b, d⟩ := bounds hL (hf j) (hf (j + 1))
  refine ⟨k, gr_part (TS γ q l m {⊤}) (l : A) r ?_ j k a b d⟩
  intro r T x h
  have e : (l : A) • x = (l : T.obj.B) * (show T.obj.B from x) := by
    rw [Algebra.smul_def, map_natCast]
  rw [e] at h
  exact T.property.1.2 _ _ h

theorem sub_trans {O A R₁ R₂ Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R₁] [CommRing R₂] [CommRing Λ]
    {I : Ideal A} {γ : DividedPowers I} {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂}
    {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂} {l n : ℕ} (d₁ : RedIn δ₁ κ₁ γ l (n + 1)) (d₂ : RedIn δ₂ κ₂ γ l n) {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} (s : ℕ) (𝒱 : Set X.Opens) {σ' : R₁ →+* R₂}
    (m : GlobalTheory.LogCris.Mor (nlFun δ₁ l X q κ₁) (nlFun δ₂ l X q κ₂) σ')
    (c₁ : Λ →+* R₁) (c₂ : Λ →+* R₂) (lam : Λ →+* A) (hc₁ : ∀ a, d₁.ρ (c₁ a) = Ideal.Quotient.mk _ (lam a))
    (hc₂ : ∀ a, d₂.ρ (c₂ a) = Ideal.Quotient.mk _ (lam a)) (h₀ : ∀ a, σ' (c₁ a) = c₂ (RingHom.id Λ a))
    (hpt : ∀ (B : CommRingCat.{0}) (y : PtOver X q κ₂ B), (show PtOver X q κ₁ B from m.pt.app B y).1.2 = y.1.2)
    (hs : Function.Surjective c₁) (r j : ℕ) (x : CH.H (B.pdS (nlFun δ₁ l X q κ₁) c₁ r).fn j) :
    (redSub q s 𝒱 d₂ c₂ lam hc₂ r).pull j ((pdOm m (RingHom.id Λ) h₀ r).pull j x) =
      trG (TS γ q l s 𝒱) (l : A) n r j ((redSub q s 𝒱 d₁ c₁ lam hc₁ r).pull j x) := by
  have hρ : ∀ x, d₂.ρ (σ' x) = lnMap (RingHom.id A) l n.le_succ (d₁.ρ x) := fun x => by
    obtain ⟨a, rfl⟩ := hs x
    rw [h₀, hc₁, hc₂]; rfl
  rw [pull_pull lam]
  change _ = (sqLe (stdI_le (TS γ q l s 𝒱) (some (r : ℤ)) (l : A) n) (stdI_le (TS γ q l s 𝒱) (some ((r : ℤ) + 1)) (l : A) n)).pull j _
  rw [pull_pull lam]
  refine (CrystallineSemistableComparison.P.prism _ _ ⟨fun T => GlobalTheory.CompanionTheory.RedTrans.eta d₁ d₂ m hpt hρ T.obj T.property.1, fun T T' f => ?_⟩
    (fun T x => ?_) j x).symm
  · refine hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl))
  · obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l (n + 1)) x
    rfl

end CrystallineSemistableComparison.HT.RhoA
end
end
