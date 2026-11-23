module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle023
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle007
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.Bundle002
public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.EqZeroOfBlockSumEqZero
public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.MapEvalRingHomOfPiFamily
import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PiSeries
public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.DistinguishedUnitIdeals.ExistsConstOfInvariantMod

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    [Fintype (K →ₐ[Qp] LL)]


variable (W) in
def EEl (i : ZMod n) : AddSubgroup W.EE where
  carrier := {ε | (letE i : LetA O n) • ε = ε ∧ ∀ δ ∈ W.DelF, W.γE δ ε = ε}
  zero_mem' := ⟨smul_zero _, fun δ _ => map_zero _⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨by rw [smul_add, ha, hb], fun δ hδ => by rw [map_add (f := _), ha' δ hδ, hb' δ hδ]⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨by rw [smul_neg, ha], fun δ hδ => by rw [map_neg, ha' δ hδ]⟩

def lc {T : LocLat G Qp LL O} {ι : Type} [Fintype ι] (b : ι → W.DD T) (c : ι → W.EE) : W.DD T :=
  ∑ j, c j • b j


variable (W) in
def LBasis (T : LocLat G Qp LL O) (i : ZMod n) {ι : Type} [Fintype ι] (b : ι → W.DD T) : Prop :=
  (∀ c : ι → W.EE, (∀ j, c j ∈ EEl W i) → lc b c ∈ DDl W T i) ∧
  (∀ c c' : ι → W.EE, (∀ j, c j ∈ EEl W i) → (∀ j, c' j ∈ EEl W i) → lc b c = lc b c' → c = c') ∧
  (∀ x ∈ DDl W T i, ∃ c : ι → W.EE, (∀ j, c j ∈ EEl W i) ∧ lc b c = x)

structure CoeffData (hR : Ring9 W) where
  M : Type
  [acg : AddCommGroup M]
  [mod : Module (PowerSeries O) M]
  κ : ZMod n → M →+ W.EE
  m₁ : M
  mem : ∀ i m, κ i m ∈ EEl W i
  surj : ∀ i, ∀ ε ∈ EEl W i, ∃ m, κ i m = ε
  inj : ∀ i, Function.Injective (κ i)
  semi : ∀ i (a : PowerSeries O) (m : M),
    κ i (a • m) = algebraMap (LetA O n) W.EE ((baseIdOf hR).d a) * κ i m
  unit : ∀ i, κ i m₁ = algebraMap (LetA O n) W.EE (letE i)

attribute [instance] CoeffData.acg CoeffData.mod

def CoeffStep (hR : Ring9 W) : Prop := Nonempty (CoeffData hR)


variable (W) in
def SplitStep : Prop :=
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
    ∃ r k : ℕ, ∀ i : ZMod n, ∃ (b₁ : Fin r ⊕ Fin k → W.DD T₁) (b₂ : Fin r → W.DD T₂),
      LBasis W T₁ i b₁ ∧ LBasis W T₂ i b₂ ∧ (∀ j, W.map F (b₁ (Sum.inl j)) = b₂ j) ∧
        ∀ j, W.map F (b₁ (Sum.inr j)) = 0


variable (W) in
def UnitStep (e : W.DD W.one) : Prop := ∀ i : ZMod n, LBasis W W.one i (fun _ : Unit => e)

section Build

variable {hR : Ring9 W} (D : CoeffData hR) {T : LocLat G Qp LL O} {ι : Type} [Fintype ι]
  (b : ZMod n → ι → W.DD T) (hb : ∀ i, LBasis W T i (b i))

def toL (i : ZMod n) : (ι → D.M) →+ ↥(DDl W T i) where
  toFun c := ⟨lc (b i) (fun j => D.κ i (c j)), (hb i).1 _ (fun j => D.mem i _)⟩
  map_zero' := by
    apply Subtype.ext
    simp [lc]
  map_add' c c' := by
    apply Subtype.ext
    simp [lc, add_smul, Finset.sum_add_distrib]

theorem toL_coe (i : ZMod n) (c : ι → D.M) :
    ((toL D b hb i c : ↥(DDl W T i)) : W.DD T) = lc (b i) (fun j => D.κ i (c j)) := rfl

theorem toL_bij (i : ZMod n) : Function.Bijective (toL D b hb i) := by
  constructor
  · intro c c' h
    have h1 := congrArg Subtype.val h
    rw [toL_coe, toL_coe] at h1
    have h2 := (hb i).2.1 _ _ (fun j => D.mem i _) (fun j => D.mem i _) h1
    funext j
    exact D.inj i (congrFun h2 j)
  · rintro ⟨x, hx⟩
    obtain ⟨c, hc, hcx⟩ := (hb i).2.2 x hx
    choose m hm using fun j => D.surj i (c j) (hc j)
    refine ⟨m, Subtype.ext ?_⟩
    rw [toL_coe]
    change lc (b i) (fun j => D.κ i (m j)) = x
    rw [← hcx]
    congr 1
    funext j
    exact hm j

def coordOf : Coord W (baseIdOf hR) T where
  V := ι → D.M
  θ i := AddEquiv.ofBijective (toL D b hb i) (toL_bij D b hb i)
  θ_smul i a c := by
    change lc (b i) (fun j => D.κ i ((a • c) j)) = (baseIdOf hR).d a • lc (b i) (fun j => D.κ i (c j))
    simp only [lc, Pi.smul_apply, D.semi, Finset.smul_sum, mul_smul, algebraMap_smul]

end Build

theorem coordSteps_of (hR : Ring9 W) (e : W.DD W.one) (hK : CoeffStep hR) (hS : SplitStep W)
    (hU : UnitStep W e) : CoordSteps hR e := by
  intro T₁ T₂ F hc₁ hc₂ hon
  obtain ⟨D⟩ := hK
  obtain ⟨r, k, hb⟩ := hS T₁ T₂ F hc₁ hc₂ hon
  choose b₁ b₂ h₁ h₂ hin hout using hb
  refine ⟨coordOf D b₁ h₁, coordOf D b₂ h₂,
    coordOf (ι := Unit) D (fun (_ : ZMod n) (_ : Unit) => e) (fun i => hU i),
    { f := LinearMap.funLeft (PowerSeries O) D.M Sum.inl
      coord_hom_map_trace := fun i c => ?_
      crys := hc₁.2.2.2
      crys' := hc₂.2.2.2 }, fun _ => D.m₁, fun i => ?_⟩
  · change ∑ j, D.κ i (c (Sum.inl j)) • b₂ i j = W.map F (∑ j, D.κ i (c j) • b₁ i j)

    rw [map_sum, Fintype.sum_sum_type]
    simp only [map_smul, hin, hout, smul_zero, Finset.sum_const_zero, add_zero]
  · change ∑ _u : Unit, D.κ i D.m₁ • e = (letE i : LetA O n) • e
    rw [Fintype.sum_unique, D.unit, algebraMap_smul]

end Formalism.MainNotions.N.Ln03
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def ExpansionFormLetter (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) : Prop :=
  ∀ (c : ZMod n) (y : W.DD T), y ∈ DelS W T → y ∈ letS W T c → (∃ k : ℕ, W.Q ^ k • y ∈ W.N T) →
    (∀ ζ τ, Pt c ζ τ → ∀ (k : ℕ) (hk : W.Q ^ k • y ∈ W.N T) (i : ℤ),
      W.levN T c ζ ⟨W.Q ^ k • y, hk⟩ i ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((k : ℤ) - i)) →
    y ∈ W.N T

end Local

def ExpansionFormAll (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K LL : FinExt l) (hG : Good K 1 LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (h' : ℕ), 1 ≤ h' → IsCrys ((D.loc l).PD K) T.ρ →
    (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
    ExpansionFormLetter ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG)

def ExpansionFormHypothesis : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → DdRFull D → DiRank D HW F Cm → ExpansionFormAll D HW

def ModelFLinkStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → ExpansionFormAll D HW → modelFR D HW

theorem modelFStep_of (hL : ModelFLinkStep) (hP : ExpansionFormHypothesis) :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
      DdRFull D → DiRank D HW F Cm → Adm1 D HW F Cm CA CB CK → modelFR D HW :=
  fun D HW F Cm CA CB CK hd hr hA => hL D HW F Cm CA CB CK hA (hP D HW F Cm CA CB CK hA hd hr)

def ModelQLinkStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelLR D HW → modelQR D HW

theorem modelQStep_of (hL : ModelQLinkStep) (hM : ModelLStep) : ModelQStep :=
  fun D HW F Cm CA CB CK hA => hL D HW F Cm CA CB CK hA (hM D HW F Cm CA CB CK hA)

end Formalism.MainNotions.N.Ln34

end
end

section

noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.Strict

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.TruncatedSeriesCountingBounds

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

section Funct

variable {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'} (f : V →ₗ[LL] V')

theorem crisMap_mulVB (c : K₀) (z : V ⊗[Qp] B) :
    crisMap B f (mulVB (LL := LL) (V := V) (B := B) c z) = mulVB (LL := LL) (V := V') (B := B) c (crisMap B f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [crisMap, mulVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem mem_DcrisL_iff (τ₀ : K₀ →ₐ[Qp] LL) (z : V ⊗[Qp] B) :
    z ∈ DcrisL PD ρ τ₀ ↔ z ∈ Dcris PD ρ ∧ ∀ c : K₀, mulVB (LL := LL) (V := V) (B := B) c z = τ₀ c • z := by
  simp [DcrisL, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

end Funct

section SES

variable {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

end SES

section P4Y

variable {PD} {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

end P4Y

section Rec

theorem p4YL (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (hL : Formalism.MainNotions.UnusedSlot80.LevCoeff D HW F) :
    Formalism.MainNotions.ArcLiftingSetup.AtCaseA fun l _ K LL hG => Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration ((HW l).W K 1 LL hG) := by
  intro l _ K LL hG hCA h5
  exact hL l K LL hCA h5

end Rec

end Formalism.MainNotions.UnusedSlot80.Strict

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Module IsLocalRing

def TeichOnto (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ a : ZMod p, a ≠ 0 → ∃ j : DeltaT p, PadicInt.toZMod (j.1 : ℤ_[p]) = a

def ComplMax : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ),
    (p : O) ∈ maximalIdeal O → (p : O) ≠ 0 → IsAdicComplete (Ideal.span {(p : O)}) O →
      IsAdicComplete (maximalIdeal O) O

def zpEquiv {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) : ℤ_[p] ≃+* ℤ_[q] := by
  subst h
  exact RingEquiv.refl _

def ιZrec {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) :
    ℤ_[(P.PD K).p] →+* ↥(OL LL) :=
  (algebraMap ℤ_[l] ↥(OL LL)).comp (zpEquiv (P.PD_p K)).toRingHom

def UTieRec (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL), 5 ≤ l →
    ∃ uZ : ℤ_[((D.loc l).PD K).p]ˣ, ((uZ : ℤ_[((D.loc l).PD K).p]) - 1).valuation = 1 ∧
      ιZrec (D.loc l) K LL uZ = (((HW l).W K 1 LL h.2.2).χΓ ((HW l).W K 1 LL h.2.2).gam : ↥(OL LL))

end Formalism.MainNotions.N.Ln03
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

theorem cyclotomicFrobeniusPowerSeries_X (W : LocWach PD LL O v n) : W.φ₀ X = (1 + X) ^ PD.p - 1 := by
  rw [W.φ₀_X, W.q₀_def]

theorem cyclo_comp_mul_X {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] :
    (Polynomial.cyclotomic p R).comp (Polynomial.X + 1) * Polynomial.X =
      (Polynomial.X + 1) ^ p - 1 := by
  rw [Polynomial.cyclotomic_prime]
  have hc : (∑ i ∈ Finset.range p, (Polynomial.X : Polynomial R) ^ i).comp (Polynomial.X + 1) =
      ∑ i ∈ Finset.range p, (Polynomial.X + 1) ^ i := by
    simp [Polynomial.comp, Polynomial.eval₂_finsetSum]
  have h := geom_sum_mul (Polynomial.X + 1 : Polynomial R) p
  rw [add_sub_cancel_right] at h
  rw [hc, h]

theorem glue2 [IsDomain O] (hR : Ring9 W) :
    ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι (baseIdOf hR).Bs.q = (w : PowerSeries O) *
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  have h0 := congrFun hw 0
  have hq : (baseIdOf hR).ι (baseIdOf hR).Bs.q = W.π₀₁ + PowerSeries.C ((PD.p : ℕ) : O) := by
    change (baseIdOf hR).ι (PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) = _
    rw [map_add (f := _), (baseIdOf hR).ι_X]
    congr 1
    exact (baseIdOf hR).ι.commutes _
  have hcyc : (W.q₀ : PowerSeries O) =
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) := by
    have hX : (PowerSeries.X : PowerSeries O) ≠ 0 := PowerSeries.X_ne_zero
    apply mul_left_cancel₀ hX
    rw [W.q₀_def]
    have := congrArg (fun f : Polynomial O => (f : PowerSeries O)) (cyclo_comp_mul_X (R := O) PD.p)
    simp only [Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_sub, Polynomial.coe_pow,
      Polynomial.coe_add, Polynomial.coe_one] at this
    rw [mul_comm, this, add_comm]
  have h0' : W.q₀ = (w : LetA O n) 0 * (W.π₀₁ + PowerSeries.C ((PD.p : ℕ) : O)) := by
    simpa [LocWach.q, Formalism.MainNotions.DeltaInvariantLattices.Eat, LocWach.π₀, Polynomial.aeval_add, Polynomial.aeval_X,
      Polynomial.aeval_C] using h0
  let w0 : (PowerSeries O)ˣ := Units.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) 0) w
  refine ⟨w0⁻¹, ?_⟩
  rw [hq, ← hcyc, h0']
  change _ = ((w0⁻¹ : (PowerSeries O)ˣ) : PowerSeries O) * ((w0 : PowerSeries O) * _)
  rw [← mul_assoc, Units.inv_mul, one_mul]

theorem rhoZ_exp [CharZero LL] (c : ZMod n) (ζ : LL) (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    1 + rhoZ W c ζ X = PowerSeries.C ζ * exp LL := by
  obtain ⟨E, h0, h1, h2⟩ := W.lev_π c ζ hζ
  have hE := (LevelStatements.Lv.expRescale LL E h0 h1).1
  rw [← hE, ← h2]
  rfl

end Formalism.MainNotions.N.Ln03
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G PowerSeries IsLocalRing

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

theorem ringSteps_of [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [CharZero LL] [IsFractionRing O LL]
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ}
    {Λ κ : PowerSeries O} {r : ℕ} {lam : Fin r → Dc W T c}
    (Hy : LvHyp Lb hR uZ ιZ C c ell Λ κ lam) (f' : PowerSeries O) (kind : ℕ → Kind) (b : ℕ → ℕ)
    (η : ℕ) (ϖ : O) (hϖ : Irreducible ϖ) (hℓ2 : PD.p ≠ 2) (hℓm : (PD.p : O) ∈ maximalIdeal O)
    (n0 : ℕ) (hn0 : ell ≤ n0) (hroot : ∃ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ n0))
    (G1 : ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι X = (w : PowerSeries O) * X ^ (PD.p - 1))
    (G2 : ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι (baseIdOf hR).Bs.q = (w : PowerSeries O) *
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O))
    (hφ : W.φ₀ X = (1 + X) ^ PD.p - 1)
    (hρζ : ∀ s < ell, ∀ ζ ∈ primitiveRoots (PD.p ^ (s + 1)) LL, 1 + rhoZ W c ζ X = PowerSeries.C ζ * exp LL)
    (huZ : ((uZ : ℤ_[PD.p]) - 1).valuation = 1) (hutie : ιZ uZ = (W.χΓ W.gam : O))
    (hom' : ∀ a : ZMod PD.p, a ≠ 0 → ∃ j : DeltaT PD.p, PadicInt.toZMod (j.1 : ℤ_[PD.p]) = a) :
    (lvModel Hy f' kind b η).K1b ∧ (lvModel Hy f' kind b η).HasU (W.χΓ W.gam) ∧
      (∀ s < ell, ((lvModel Hy f' kind b η).lev s).FiniteOrderFixed (baseIdOf hR).Bs.ℓ s ∧
        ((lvModel Hy f' kind b η).lev s).PhiGammaCommute) ∧
      (lvModel Hy f' kind b η).UnitsAt ∧ (lvModel Hy f' kind b η).Compl ϖ := by
  obtain ⟨w, hw⟩ := G1
  exact LevelStatements.Link.linkRing LevelStatements.Lv.rhoUnique LevelStatements.Lv.splitCompl LevelStatements.Lv.cycloSimple
    LevelStatements.Lv.psCoprime LevelStatements.Lv.rhoUnit LevelStatements.Lv.descendDvd LevelStatements.Lv.piSeries ϖ hϖ
    (lvData Hy f' kind b η) (hℓ := ⟨PD.hp⟩) hℓ2 hℓm n0 hn0 hroot (baseIdOf hR).ι w hw W.φ₀ hφ
    (baseIdOf hR).ι_φ LevelStatements.Lv.psCyclo G2 (rhoZ W c) hρζ (lvModel Hy f' kind b η)
    (fun s _ a ζ => map_eval_rhoL hR c s a ζ) (W.χΓ W.gam) (uZ : ℤ_[PD.p]) huZ ιZ hutie
    (fun _ _ => rfl)
    (fun s _ f ζ ζ' h => by
      change f (powR LL PD.p s _ ζ) = f ζ'
      congr 1
      apply Subtype.ext
      rw [h]
      rfl)
    (fun j => (j.1 : ℤ_[PD.p]))
    (fun j => (by simpa using congrArg (fun x : ℤ_[PD.p]ˣ => (x : ℤ_[PD.p])) j.2 :
      ((j.1 : ℤ_[PD.p])) ^ (PD.p - 1) = 1))
    hom'
    (fun s _ j f ζ ζ' h => by
      change f (powR LL PD.p s _ ζ) = f ζ'
      congr 1
      apply Subtype.ext
      rw [h]
      rfl)

end Formalism.MainNotions.N.Ln03
end
end
