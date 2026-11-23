module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle004
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.Bundle001

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def WtRed : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ (S : Type) [CommRing S] [IsReduced S] [Algebra c.F S]
    (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y

theorem wtRed_of (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    (hA : AllTest Xo c) (hW : WtField Xo c) (hB : FrBCFieldSt Xo c) : WtRed Xo c := by
  intro a n f hf S _ _ _ t y y' hb
  have hN := evNat_of Xo c hWD hA
  rw [← sub_eq_zero]
  set d := evR Xo c f y' - wchar (ex Dw a n) t * evR Xo c f y with hd
  have hP : ∀ P : Ideal S, P.IsPrime → d ∈ P := by
    intro P hPp
    have := hPp
    let ρ : S →+* FractionRing (S ⧸ P) := (algebraMap (S ⧸ P) (FractionRing (S ⧸ P))).comp (Ideal.Quotient.mk P)
    let _ : Algebra c.F (FractionRing (S ⧸ P)) := (ρ.comp (algebraMap c.F S)).toAlgebra
    let φ : S →ₐ[c.F] FractionRing (S ⧸ P) := { ρ with commutes' := fun _ => rfl }
    obtain ⟨z, hz⟩ := hB S y (FractionRing (S ⧸ P)) φ
    obtain ⟨z', hz'⟩ := hB S y' (FractionRing (S ⧸ P)) φ
    have hbz := frBorBC (Xo := Xo) (c := c) S (FractionRing (S ⧸ P)) φ t y y' z z' hb hz hz'
    have e1 := hN f hf.1 S (FractionRing (S ⧸ P)) φ y z hz
    have e2 := hN f hf.1 S (FractionRing (S ⧸ P)) φ y' z' hz'
    have e3 := hW a n f hf (FractionRing (S ⧸ P)) _ z z' (hA _ z) (hA _ z') hbz
    have hw : φ (wchar (ex Dw a n) t) = wchar (ex Dw a n) (fun i => Units.map (φ : S →* FractionRing (S ⧸ P)) (t i)) := by
      simp only [wchar, map_prod, map_pow, Units.coe_map, MonoidHom.coe_coe]
    have h0 : φ d = 0 := by
      rw [hd, map_sub, map_mul, ← e1, ← e2, e3, hw, sub_self]
    have h1 : algebraMap (S ⧸ P) (FractionRing (S ⧸ P)) (Ideal.Quotient.mk P d) = 0 := h0
    have h2 : Ideal.Quotient.mk P d = 0 :=
      (IsFractionRing.injective (S ⧸ P) (FractionRing (S ⧸ P))) (by rw [h1, map_zero])
    exact Ideal.Quotient.eq_zero_iff_mem.mp h2
  have hnil : d ∈ nilradical S := by
    rw [nilradical_eq_sInf]
    exact Submodule.mem_sInf.mpr fun Q hQ => hP Q hQ
  exact IsReduced.eq_zero d (mem_nilradical.mp hnil)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section



noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

section Comparison₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]

def SecTieK {t : SAB H (Sp V)} {tK : SAB H (Sp (FractionRing V))} (m : SABMap tK t (Out.jK V))
    (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)) (k : ℕ)
    (F : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V))))))
    (σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => (k : ℤ)))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ tK.G.left) (zp : Z ⟶ (𝟙_ (Over (Sp (FractionRing V))) ⊗ tK.G).left),
    zp ≫ (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left = r →
    ∀ (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) (J' : (Z ⟶ tK.G.left) → tK.PP.L.ι),
      Good t.PP.L z J → Good tK.PP.L z J' →
      sval σ (r ≫ m.φ) z J = ((gv w r z (fun _ => J (r ≫ m.φ)) (J' (r ≫ 𝟙 _))).val) ^ k * sval F zp z J'

end Comparison₂

def RegUnifSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ θ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((1 : ℕ) : ℤ))),
      (∀ σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((1 : ℕ) : ℤ))),
        ∃! a : V, ∀ i, σ.f i = resG t.G.left le_top ((t.G.hom).appTop.hom (toΓ V a)) * θ.f i) →
    ∀ (M : ℕ), IsUnit (M : V) →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (θK : LB.Sec (LPow tK.G tK.PP.L ((1 : ℕ) : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))), SecTieK m w 1 θK θ →
    ∀ (t₀ : 𝟙_ (Over (Sp (FractionRing V))) ⟶ tK.G)
      (F : LB.Sec (LPow tK.G tK.PP.L ((M : ℤ) ^ 2) (𝟙_ (Over (Sp (FractionRing V)))))),
      IsVtOver tK.G tK.PP M (fun u => u ^ (M ^ 2) = 1) (zCast tK.G (Nat.cast_one) θK) t₀ F →
      ∃ σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((M ^ 2 : ℕ) : ℤ))),
        SecTieK m w (M ^ 2) (zCast tK.G (natCast_sq M) F) σ

section Move

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def TieMv {X₀ : Scheme.{0}} {t₀ : SAB H X₀} {K : Type} [Field K] {x : Sp K ⟶ X₀} {tK : SAB H (Sp K)}
    (m1 : SABMap tK t₀ x) (w1 : LB.Iso tK.PP.L (t₀.PP.L.pull m1.φ)) (k : ℕ)
    (F : LB.Sec (LPow t₀.G t₀.PP.L (k : ℤ) (Over.mk x)))
    (FK : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp K))))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ tK.G.left) (zp : Z ⟶ (Over.mk x ⊗ t₀.G).left)
    (zp' : Z ⟶ (𝟙_ (Over (Sp K)) ⊗ tK.G).left),
    zp ≫ (snd (Over.mk x) t₀.G).left = r ≫ m1.φ → zp ≫ (fst (Over.mk x) t₀.G).left = r ≫ tK.G.hom →
    zp' ≫ (snd (𝟙_ (Over (Sp K))) tK.G).left = r →
    ∀ (z : Z) (J : (Z ⟶ t₀.G.left) → t₀.PP.L.ι) (J' : (Z ⟶ tK.G.left) → tK.PP.L.ι),
      Good t₀.PP.L z J → Good tK.PP.L z J' →
      sval F zp z J = ((gv w1 r z (fun _ => J (r ≫ m1.φ)) (J' (r ≫ 𝟙 _))).val) ^ k * sval FK zp' z J'

end Move

def VtMoveSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X₀ : Scheme.{0}) (t₀ : SAB H X₀)
    (K : Type) [Field K] (x : Sp K ⟶ X₀) (tK : SAB H (Sp K)) (m1 : SABMap tK t₀ x)
    (w1 : LB.Iso tK.PP.L (t₀.PP.L.pull m1.φ)), RigIso m1 w1 →
    ∀ (N : ℕ) (ok : (Over.mk x ⟶ t₀.G) → Prop) (s : LB.Sec (LPow t₀.G t₀.PP.L 1 (Over.mk x)))
      (tt : Over.mk x ⟶ t₀.G) (F : LB.Sec (LPow t₀.G t₀.PP.L ((N : ℤ) ^ 2) (Over.mk x))),
      IsVtOver t₀.G t₀.PP N ok s tt F → (∀ u, ok u → u ^ (N ^ 2) = 1) →
    ∀ sK : LB.Sec (LPow tK.G tK.PP.L ((1 : ℕ) : ℤ) (𝟙_ (Over (Sp K)))),
      TieMv m1 w1 1 (zCast t₀.G Nat.cast_one.symm s) sK →
      ∃ (ttK : 𝟙_ (Over (Sp K)) ⟶ tK.G) (FK : LB.Sec (LPow tK.G tK.PP.L ((N : ℤ) ^ 2) (𝟙_ (Over (Sp K))))),
        IsVtOver tK.G tK.PP N (fun u => u ^ (N ^ 2) = 1) (zCast tK.G Nat.cast_one sK) ttK FK ∧
        TieMv m1 w1 (N ^ 2) (zCast t₀.G (natCast_sq N) F) (zCast tK.G (natCast_sq N) FK)

def ThetaTieSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (Tc : CDVR) (io : c.F →+* Tc.Fr) (y : letI := io.toAlgebra; FrPt Xo c Tc.Fr)
    (I : IntData Xo c Tc io y),
    letI := io.toAlgebra
    ∃ θ : LB.Sec (LB.LinComb I.G.PP.L (K := Fin 1) (fun _ => 𝟙 I.G.G.left) (fun _ => ((1 : ℕ) : ℤ))),
      (∀ σ : LB.Sec (LB.LinComb I.G.PP.L (K := Fin 1) (fun _ => 𝟙 I.G.G.left) (fun _ => ((1 : ℕ) : ℤ))),
        ∃! a : Tc.V, ∀ i, σ.f i = resG I.G.G.left le_top ((I.G.G.hom).appTop.hom (toΓ Tc.V a)) * θ.f i) ∧
      ∃ θK : LB.Sec (LPow I.t'.G I.t'.PP.L ((1 : ℕ) : ℤ) (𝟙_ (Over (Sp Tc.Fr)))),
        TieMv I.m1 I.w1 1 (zCast Xo.univ.t.G Nat.cast_one.symm y.s) θK ∧ SecTieK I.m2 I.w2 1 θK θ

section Restrict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}

def gsec (G : Over S) : G.left ⟶ (𝟙_ (Over S) ⊗ G).left := (lift (toUnit G) (𝟙 G)).left

theorem gsec_snd (G : Over S) : gsec G ≫ (snd (𝟙_ (Over S)) G).left = 𝟙 _ := by
  rw [gsec, ← Over.comp_left, lift_snd, Over.id_left]

theorem exists_restrict (t : SAB H S) (a : ℤ) (F : LB.Sec (LPow t.G t.PP.L a (𝟙_ (Over S)))) :
    ∃ σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => a)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
        sval σ r z J = sval F (r ≫ gsec t.G) z J := by
  have hF : FormEq (Sum.elim (fun k => gsec t.G ≫ (fun _ : Fin 1 => (snd (𝟙_ (Over S)) t.G).left) k)
      (PEmpty.elim : PEmpty → _)) (Sum.elim (fun _ : Fin 1 => a) (PEmpty.elim : PEmpty → ℤ))
      (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => a) := by
    intro U _ h
    have e := gsec_snd t.G
    simp only [Fintype.prod_sum_type, Sum.elim_inl, e, Finset.univ_eq_empty, Finset.prod_empty, _root_.mul_one]
  obtain ⟨σ, hσ⟩ := exists_sec t.PP.isLB hF
    (pullMulSec (F : LB.Sec (LB.LinComb t.PP.L (fun _ : Fin 1 => (snd (𝟙_ (Over S)) t.G).left) (fun _ => a)))
      (gsec t.G) (LB.oneGen t.PP.L) (fun _ _ => by dsimp only [LB.oneGen]; erw [map_one, map_one, _root_.mul_one]; simp [LB.LinComb]; rfl))
  refine ⟨σ, fun Z r z J hJ => ?_⟩
  refine (hσ Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ r z hJ).trans ?_)
  rw [val_one, Units.val_one, _root_.mul_one]

end Restrict

theorem isUnit_natCast_of_overLa {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} (Tc : CDVR)
    {io : K →+* Tc.Fr} {e : ℕ} (ho : OverLa la Tc.V io e) {M : ℕ} (hM : (M : 𝓞 K) ∉ la.asIdeal) :
    IsUnit (M : Tc.V) := by
  have h1 : la.valuation K (M : K) = 1 := by
    have e1 : (M : K) = algebraMap (𝓞 K) K (M : 𝓞 K) := by simp
    rw [e1, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hM
  have h2 := ho.2 (M : K)
  rw [vLa, h1, WithZero.log_one, neg_zero, mul_zero, map_natCast] at h2
  have e2 : ((M : ℕ) : Tc.Fr) = algebraMap Tc.V Tc.Fr (M : Tc.V) := by simp
  rw [e2, vV, valV, HeightOneSpectrum.valuation_of_algebraMap, neg_eq_zero] at h2
  have hne : (IsDiscreteValuationRing.maximalIdeal Tc.V).intValuation (M : Tc.V) ≠ 0 := by
    refine HeightOneSpectrum.intValuation_ne_zero _ _ ?_
    intro h0
    apply hM
    have : M = 0 := by exact_mod_cast h0
    rw [this, Nat.cast_zero]; exact la.asIdeal.zero_mem
  have h3 : (IsDiscreteValuationRing.maximalIdeal Tc.V).intValuation (M : Tc.V) = 1 := by
    rw [← WithZero.exp_log hne, h2, WithZero.exp_zero]
  rw [HeightOneSpectrum.intValuation_eq_one_iff] at h3
  by_contra hu
  exact h3 ((IsLocalRing.mem_maximalIdeal _).2 hu)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

section Abstract

variable {K : Type*} [Field K] {σ : K →+* ℂ} {C : Type*} [AddCommGroup C] [Module K C]
  {W : Type*} [AddCommGroup W] [Module ℂ W]

def IndepToC (j : C →ₛₗ[σ] W) : Prop :=
  ∀ (n : ℕ) (b : Fin n → C), LinearIndependent K b → LinearIndependent ℂ (fun i => j (b i))

theorem map_mem_span_of_mem_span (j : C →ₛₗ[σ] W) (T : Set C) {x : C}
    (hx : x ∈ Submodule.span K T) : j x ∈ Submodule.span ℂ (j '' T) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => simp
  | add y w _ _ hy hw => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hw
  | smul a y _ hy => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

theorem span_eq_top_of_indepToC (j : C →ₛₗ[σ] W) (hj : IndepToC j) (S : Set C)
    (hS : ∀ f, j f ∈ Submodule.span ℂ (j '' S)) : Submodule.span K S = ⊤ := by
  classical
  rw [eq_top_iff]
  intro f _
  by_contra hf
  obtain ⟨T, hTS, hfT⟩ := Submodule.mem_span_finite_of_mem_span (hS f)
  obtain ⟨T', hT'S, rfl⟩ := Finset.subset_set_image_iff.mp hTS
  obtain ⟨b, hbT, hspan, hli⟩ := exists_linearIndependent K (T' : Set C)
  have hbfin : b.Finite := (T'.finite_toSet).subset hbT

  have hjf : j f ∈ Submodule.span ℂ (j '' b) := by
    have hle : Submodule.span ℂ ((T'.image j : Finset W) : Set W) ≤ Submodule.span ℂ (j '' b) := by
      rw [Submodule.span_le]
      intro y hy
      rw [Finset.coe_image] at hy
      obtain ⟨t, ht, rfl⟩ := hy
      apply map_mem_span_of_mem_span
      rw [hspan]
      exact Submodule.subset_span ht
    exact hle hfT

  have hfb : f ∉ Submodule.span K b := by
    intro h
    apply hf
    rw [hspan] at h
    exact Submodule.span_mono hT'S h
  have hli' : LinearIndependent K (fun y : ↥(insert f b) => (y : C)) :=
    LinearIndepOn.insert (v := id) (s := b) (x := f) hli (by simpa using hfb)
  have hfin : (insert f b).Finite := hbfin.insert f
  haveI := hfin.fintype
  let e := Fintype.equivFin ↥(insert f b)
  have hC := hj _ (fun i => ((e.symm i : ↥(insert f b)) : C)) (hli'.comp _ e.symm.injective)
  have hC' : LinearIndependent ℂ (fun y : ↥(insert f b) => j (y : C)) := by
    have := hC.comp _ e.injective
    simpa [Function.comp_def] using this
  have hnot := hC'.notMem_span_image (s := {y : ↥(insert f b) | (y : C) ∈ b})
    (x := ⟨f, Set.mem_insert f b⟩) (by
      intro hx
      exact hfb (Submodule.subset_span hx))
  apply hnot
  convert hjf using 2
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, Set.mem_insert_of_mem f hz⟩, hz, rfl⟩

end Abstract

theorem spanAt_of_chain {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    (ka : WeightFamilies.Wt D j) {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : B.KO →+* ℂ}
    (J : B.Cusp j ka →ₛₗ[σ] W) (hJ : IndepToC J) (Sp : Submodule ℂ W) (A : Set W)
    (hmem : ∀ f, J f ∈ Sp) (hsp : Sp ≤ Submodule.span ℂ A)
    (hA : A ⊆ Submodule.span ℂ (J '' ((X.shortTh ka : Submodule (𝓞 B.KO) (B.Cusp j ka)) : Set (B.Cusp j ka)))) :
    SpanAt X ka := by
  unfold SpanAt
  apply span_eq_top_of_indepToC J hJ
  intro f
  have h1 : Submodule.span ℂ A ≤
      Submodule.span ℂ (J '' ((X.shortTh ka : Submodule (𝓞 B.KO) (B.Cusp j ka)) : Set (B.Cusp j ka))) := by
    rw [Submodule.span_le]
    exact hA
  exact h1 (hsp (hmem f))

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.TB

theorem latOfLam : LatOfLamSt := by
  intro D B P j X S ka wL wF large₂ C A hg hs hlam hspan hH2
  let Nf : NormFam B.KO (B.Cusp j ka) :=
    { N := B.supN j ka
      nonneg := B.supN_nonneg j ka
      eq_zero := fun σ v h => (B.supN_eq_zero j ka σ v).mp h
      smul := B.supN_smul j ka
      add := B.supN_add j ka }
  have hPL : ProdLower Nf (B.Mlat j ka)
      ((Fintype.card (B.KO →+* ℂ) : ℝ) * (WeightFamilies.PP0v D large₂ C A * (1 + Real.log ka.size) * ka.size)) := by
    intro f hf hne
    have h1 := hlam f hf hne
    unfold WeightFamilies.meanLogSup at h1
    by_cases hc : (Fintype.card (B.KO →+* ℂ) : ℝ) = 0
    · have hc' : Fintype.card (B.KO →+* ℂ) = 0 := by exact_mod_cast hc
      have hempty : IsEmpty (B.KO →+* ℂ) := Fintype.card_eq_zero_iff.mp hc'
      rw [hc, zero_mul, neg_zero]
      simp
    · have hpos : (0 : ℝ) < Fintype.card (B.KO →+* ℂ) :=
        lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hc)
      have h2 := (le_div_iff₀ hpos).mp h1
      show -((Fintype.card (B.KO →+* ℂ) : ℝ) * _) ≤ ∑ σ : B.KO →+* ℂ, Real.log (B.supN j ka σ f)
      linarith
  have hUD := discriminant_of_product_lower B.KO (B.Cusp j ka) Nf (B.Mlat j ka) _ hPL
  have hFG := formalGroup_of_discriminant B.KO (B.Cusp j ka) Nf (B.Mlat j ka) hUD
  exact Submodule.IsLattice.of_fg B.KO hFG

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
