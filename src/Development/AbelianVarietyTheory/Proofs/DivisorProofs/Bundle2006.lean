module

public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle009
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle820
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle305
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.FrobeniusSumFormula
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle042
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1964
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1296
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

theorem GlobalTheory.RightTranslateFundDomain.haar_and_fundDomain : ∀ {D : D7} {V : HSp D} (m : MeasureTheory.Measure (GA D V)) (fd : Set (GA D V)) (g : GA D V), m.IsHaarMeasure → MeasureTheory.IsFundamentalDomain (GQ V) fd m → (m.map (fun x => x * g⁻¹)).IsHaarMeasure ∧ MeasureTheory.IsFundamentalDomain (GQ V) ((fun x => x * g) ⁻¹' fd) (m.map (fun x => x * g⁻¹)) := by
  intro D V m fd g hm hfd
  have hmeas : Measurable (fun x : GA D V => x * g⁻¹) := measurable_mul_const g⁻¹
  refine ⟨?_, ?_⟩
  · have h := Measure.isHaarMeasure_map_mul_right m g⁻¹
    exact h
  · refine hfd.preimage_of_equiv (e := id) ?_ Function.bijective_id ?_
    · refine ⟨(measurable_mul_const g).aemeasurable, ?_⟩
      rw [Measure.map_map (measurable_mul_const g) hmeas]
      have : ((fun x : GA D V => x * g) ∘ fun x => x * g⁻¹) = id := by
        funext x; simp
      rw [this, Measure.map_id]
    · intro h x
      show (h • x) * g = h • (x * g)
      simp [Submonoid.smul_def, Subgroup.smul_def, mul_assoc]
end

section

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES

noncomputable section

namespace GlobalTheory.HCInduction

open Formalism.L2.DIV GlobalTheory.BI

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

theorem parab_eq_blockTri (b : Fin r → Fin s) :
    parab K b = blockTri (κ := K) (fun i => (b i : ℕ)) := by
  ext g
  constructor
  · intro hg
    exact hg.1
  · intro hg
    exact ⟨hg, (blockTri (κ := K) (fun i => (b i : ℕ))).inv_mem hg⟩


omit [Fintype K] [DecidableEq K] in
def blockGL (b : Fin r → Fin s) (c : Fin s) :
    GL (Fin (Fintype.card {i // b i = c})) K ≃* GL {i // b i = c} K :=
  glEquiv K (Fintype.equivFin {i // b i = c}).symm

omit [Fintype K] [DecidableEq K] in
theorem blockGL_apply (b : Fin r → Fin s) (c : Fin s) (g : GL (Fin (Fintype.card {i // b i = c})) K)
    (x y : {i // b i = c}) :
    ((blockGL b c g : GL {i // b i = c} K) : Matrix _ _ K) x y =
      (g : Matrix _ _ K) (Fintype.equivFin _ x) (Fintype.equivFin _ y) := rfl

theorem sum_unipRadical_eq_zero (b : Fin r → Fin s) (c : Fin s) (τ : FDRep ℂ (GL {i // b i = c} K))
    (hτ : IsCuspidal K τ) (c' : Fin (Fintype.card {i // b i = c}) → ℕ) (hc' : ∃ i j, c' i ≠ c' j) :
    ∑ᶠ u : GlobalTheory.FiniteGL.unipRadical K c', LinearMap.trace ℂ τ (τ.ρ (blockGL b c u)) = 0 := by
  classical
  let _ : Fintype (GlobalTheory.FiniteGL.unipRadical K c') := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  let ρu : Representation ℂ (GlobalTheory.FiniteGL.unipRadical K c') τ :=
    τ.ρ.comp ((blockGL b c).toMonoidHom.comp (GlobalTheory.FiniteGL.unipRadical K c').subtype)
  refine (GlobalTheory.GoodTypeGeneric.sum_character_eq_zero_iff ρu).2 ?_
  intro v hv
  obtain ⟨i0, j0, h0⟩ : ∃ i0 j0, c' i0 < c' j0 := by
    obtain ⟨i, j, hij⟩ := hc'
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h⟩
    · exact ⟨j, i, h⟩
  let F := Fintype.equivFin {i // b i = c}
  let bb : {i // b i = c} → Fin 2 := fun x => if c' (F x) ≤ c' i0 then 0 else 1
  have hbb : Function.Surjective bb := by
    intro k
    fin_cases k
    · exact ⟨F.symm i0, by simp [bb]⟩
    · exact ⟨F.symm j0, by simp [bb, not_le.2 h0]⟩
  refine hτ 2 bb hbb le_rfl v fun u hu => ?_
  set u' := (blockGL b c).symm u with hu'def
  have hu'u : blockGL b c u' = u := MulEquiv.apply_symm_apply _ _
  have hent : ∀ k l, (u' : Matrix _ _ K) k l = (u : Matrix _ _ K) (F.symm k) (F.symm l) := by
    intro k l
    rw [← hu'u, blockGL_apply]
    simp [F]
  have hmem : u' ∈ GlobalTheory.FiniteGL.unipRadical K c' := by
    rw [GlobalTheory.FiniteGL.mem_unipRadical]
    intro k l hlk
    rw [Matrix.sub_apply, hent]
    have hb : ∀ m, bb (F.symm m) = if c' m ≤ c' i0 then 0 else 1 := fun m => by simp [bb]
    by_cases hkl : bb (F.symm k) = bb (F.symm l)
    · rw [hu.2 _ _ hkl]
      by_cases e : k = l
      · subst e; simp
      · rw [if_neg (fun h => e (F.symm.injective h)), Matrix.one_apply_ne e, sub_zero]
    · have hk : ¬ c' k ≤ c' i0 := fun hk => hkl (by rw [hb, hb, if_pos hk, if_pos (hlk.trans hk)])
      have hl : c' l ≤ c' i0 := by
        by_contra hl
        exact hkl (by rw [hb, hb, if_neg hk, if_neg hl])
      have hlt : bb (F.symm l) < bb (F.symm k) := by
        rw [hb, hb, if_neg hk, if_pos hl]; decide
      have ekl : k ≠ l := fun e => hkl (by rw [e])
      rw [hu.1.1 _ _ hlt, Matrix.one_apply_ne ekl, sub_zero]
  have := hv ⟨u', hmem⟩
  simpa [ρu, hu'u] using this

theorem isIrrChar_block (b : Fin r → Fin s) (c : Fin s) (τ : FDRep ℂ (GL {i // b i = c} K)) (hτ : Simple τ) :
    IsIrrChar ℂ ℂ (fun g : GL (Fin (Fintype.card {i // b i = c})) K => LinearMap.trace ℂ τ (τ.ρ (blockGL b c g))) := by
  have hi := GlobalTheory.FinGL.Transport.isIrreducible_comp τ.ρ (blockGL b c).toMonoidHom (blockGL b c).surjective
    (GlobalTheory.SerOSys.ZSum.isIrreducible_of_simple τ hτ)
  have h := (isChar_and_isIrrChar_of_rep ℂ ℂ _ τ (τ.ρ.comp (blockGL b c).toMonoidHom)).2 hi
  simpa [Representation.character] using h

theorem isCuspProdChar_trace_hcRep : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), Function.Surjective b →
    (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → Monotone b →
    GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (fun x : GL (Fin r) K => LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x)) := by
  intro K _ _ _ r s b lam _ hlam hmono
  classical
  let b₀ : Fin r → ℕ := fun i => (b i : ℕ)
  have hb₀ : Monotone b₀ := fun i j h => hmono h
  let d : Fin s → ℕ := fun c => Fintype.card {i // b i = c}
  let e : (Σ c, Fin (d c)) ≃ Fin r :=
    (Equiv.sigmaCongrRight fun c => (Fintype.equivFin {i // b i = c}).symm).trans (Equiv.sigmaFiberEquiv b)
  have hbe : ∀ x, b (e x) = x.1 := fun x => ((Fintype.equivFin {i // b i = x.1}).symm x.2).2
  have he : ∀ x y, b₀ (e x) = b₀ (e y) ↔ x.1 = y.1 := by
    intro x y
    simp only [b₀, hbe, Fin.val_inj]
  let χ : ∀ c, GL (Fin (d c)) K → ℂ := fun c g => LinearMap.trace ℂ (lam c) ((lam c).ρ (blockGL b c g))
  obtain ⟨n, σ, hσ, hch⟩ := GlobalTheory.GoodTypeGeneric.exists_isCuspDatum (F := K) hb₀ e he χ
    (fun c => isIrrChar_block b c (lam c) (hlam c).1)
    (fun c c' hc' => sum_unipRadical_eq_zero b c (lam c) (hlam c).2 c' hc')
  refine ⟨n, b₀, σ, hσ, fun x => ?_⟩
  have hPB := parab_eq_blockTri (K := K) b
  let f : blockTri (κ := K) b₀ →* parab K b :=
    MonoidHom.codRestrict (blockTri (κ := K) b₀).subtype (parab K b) (fun p => by rw [hPB]; exact p.2)
  have hf : Function.Surjective f := fun p => ⟨⟨p.1, by rw [← hPB]; exact p.2⟩, rfl⟩
  have h1 : LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x) =
      (Representation.coind (parab K b).subtype (PI.SerBridgeGLW.inflRep K b lam)).character x := rfl
  show LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x) = _
  have h2 := GlobalTheory.FinGL.Transport.character_coind (parab K b).subtype (blockTri (κ := K) b₀).subtype
    (PI.SerBridgeGLW.inflRep K b lam) (MulEquiv.refl _) f hf (fun _ => rfl) x
  rw [MulEquiv.refl_apply] at h2
  rw [h1, ← h2]
  rw [GlobalTheory.GoodTypeGeneric.character_coind_eq_ind, GlobalTheory.GoodTypeGeneric.character_coind_eq_ind]
  congr 1
  funext p
  rw [hch p]
  show LinearMap.trace ℂ _ (PiTensorProduct.map fun c => (lam c).ρ (levi K b c (f p))) = _
  rw [PI.SerBridgeGLW.trace_piTensorMap]
  refine Finset.prod_congr rfl fun c _ => ?_
  show _ = LinearMap.trace ℂ (lam c) ((lam c).ρ (blockGL b c _))
  congr 3
  apply Units.ext
  ext x y
  rw [blockGL_apply, GlobalTheory.GoodTypeGeneric.blocksHom_apply]
  have hx : ∀ z : {i // b i = c}, e ⟨c, Fintype.equivFin _ z⟩ = z.1 := fun z => by
    simp [e, Equiv.sigmaFiberEquiv]
  rw [hx, hx]
  rfl

end GlobalTheory.HCInduction
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two.HomConst

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegPre R} {e : ℕ}
  {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]

theorem torusHomOf_iff_appTop {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']
    (h : X' → X) (t : splitTorus S X ⟶ splitTorus S X') : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X' χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X' χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X' χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

def Acts (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    (a : (thickObj R I e G₁).left ⟶ (thickObj R I e G₂).left) (f : D₂.X → D₁.X) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J₁ : (Z ⟶ D₁.P.A.left) → D₁.P.L.ι)
    (J₂ : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D₁.P.L z J₁ → Good D₂.P.L z J₂ →
    r ≫ g₁.pG.left = r ≫ (fstG I e G₁).left ≫ G₁.hom ≫ eSec D₁.P.A →
    ∀ x, val (g₂.t x) (r ≫ a) z J₂ = val (g₁.t (f x)) r z J₁

theorem acts_of_torusHomOf (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    (a : thickObj R I e G₁ ⟶ thickObj R I e G₂) {f : D₂.X → D₁.X}
    {t : splitTorus _ D₁.X ⟶ splitTorus _ D₂.X} (ht : TorusHomOf f t)
    (hi : g₁.i ≫ a = t ≫ g₂.i) : Acts g₁ g₂ a.left f := by
  intro Z r z J₁ J₂ hJ₁ hJ₂ h x
  let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    Over.mk (r ≫ (thickObj R I e G₁).hom)
  let b : FinalForm ⟶ thickObj R I e G₁ := Over.homMk r rfl
  let τ := g₁.isKernel.lift b (toUnit _) ((CharAgree.comp_q_eq_one_iff g₁ b).2 h)
  have hτ : τ ≫ g₁.i = b := g₁.isKernel.lift_fst _ _ _
  have hτ' : (τ ≫ t) ≫ g₂.i = b ≫ a := by rw [Category.assoc, ← hi, ← Category.assoc, hτ]
  have k := (TorusCoord.val_torus_point_and_translate R I D₂ e G₂ g₂ FinalForm (τ ≫ t) 1 z J₂ hJ₂ x).1
  have k' := (TorusCoord.val_torus_point_and_translate R I D₁ e G₁ g₁ FinalForm τ 1 z J₁ hJ₁ (f x)).1
  rw [hτ'] at k
  rw [hτ] at k'
  refine k.trans (Eq.trans (Units.ext ?_) k'.symm)
  rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial]
  refine congrArg (FinalForm.left.presheaf.germ ⊤ z trivial).hom ?_
  exact (SplitTorusHom.appTop_comp τ t _).trans
    (congrArg τ.left.appTop.hom ((torusHomOf_iff_appTop _ _).1 ht x))

theorem acts_unique [IsAdicComplete I R] (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    {a : (thickObj R I e G₁).left ⟶ (thickObj R I e G₂).left} {f f' : D₂.X → D₁.X}
    (h : Acts g₁ g₂ a f) (h' : Acts g₁ g₂ a f') : f = f' := by
  funext x
  have := EndTorus.connectedSpace_thickening I e
  refine SplitTorusHom.charUnit_injective (S := Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (congrArg Units.val (unit_ext fun z _ => ?_))
  choose J₁ hJ₁ using fun ψ : (splitTorus _ D₁.X).left ⟶ D₁.P.A.left => exists_chart D₁.P.isLB (ψ z)
  choose J₂ hJ₂ using fun ψ : (splitTorus _ D₁.X).left ⟶ D₂.P.A.left => exists_chart D₂.P.isLB (ψ z)
  have c := (CharAgree.comp_q_eq_one_iff g₁ g₁.i).1 g₁.isKernel.w
  have k := fun χ =>
    (TorusCoord.val_torus_point_and_translate R I D₁ e G₁ g₁ _ (𝟙 _) 1 z J₁ hJ₁ χ).1
  simp only [Category.id_comp] at k
  exact (k _).symm.trans (((h _ _ z J₁ J₂ hJ₁ hJ₂ c x).symm.trans (h' _ _ z J₁ J₂ hJ₁ hJ₂ c x)).trans (k _))


omit [IsDomain R] [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] in
theorem thickMap_comm (aG : G₁ ⟶ G₂) (e : ℕ) :
    thickMap R I e G₁ ≫ ((Over.pullback (thick R I (e + 1))).map aG).left =
      ((Over.pullback (thick R I e)).map aG).left ≫ thickMap R I e G₂ := by
  apply pullback.hom_ext <;>
    simp [thickMap, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc]

theorem acts_down {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))}
    (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (aG : G₁ ⟶ G₂)
    {f : D₂.toPre.X → D₁.toPre.X}
    (h : Acts (U₁.gt (e + 1)) (U₂.gt (e + 1)) ((Over.pullback (thick R I (e + 1))).map aG).left f) :
    Acts (U₁.gt e) (U₂.gt e) ((Over.pullback (thick R I e)).map aG).left f := by
  intro Z r z J₁ J₂ hJ₁ hJ₂ c x
  have t : thickMap R I e G₁ ≫ (fstG I (e + 1) G₁).left = (fstG I e G₁).left :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have up : (r ≫ thickMap R I e G₁) ≫ (U₁.gt (e + 1)).pG.left =
      (r ≫ thickMap R I e G₁) ≫ (fstG I (e + 1) G₁).left ≫ G₁.hom ≫ eSec D₁.toPre.P.A := by
    refine (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (U₁.gt_q e)).trans (c.trans ?_))
    refine Eq.trans (congrArg (r ≫ ·) ?_) (Category.assoc _ _ _).symm
    exact (congrArg (· ≫ G₁.hom ≫ eSec D₁.toPre.P.A) t.symm).trans (Category.assoc _ _ _)
  have k := h Z (r ≫ thickMap R I e G₁) z J₁ J₂ hJ₁ hJ₂ up x
  have sq : (r ≫ thickMap R I e G₁) ≫ ((Over.pullback (thick R I (e + 1))).map aG).left =
      (r ≫ ((Over.pullback (thick R I e)).map aG).left) ≫ thickMap R I e G₂ := by
    rw [Category.assoc, Category.assoc, thickMap_comm]
  rw [sq] at k
  exact (val_corr hJ₂ (U₂.gt_t e x) _).symm.trans ((val_pull hJ₂ _ _ _).trans (k.trans
    ((val_pull hJ₁ _ _ _).symm.trans (val_corr hJ₁ (U₁.gt_t e (f x)) r))))

theorem exists_torus_hom (hR : AdmBase R I) (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    (a : thickObj R I e G₁ ⟶ thickObj R I e G₂) [IsMonHom a] :
    ∃ h : D₂.X →+ D₁.X, ∃ t, TorusHomOf h t ∧ g₁.i ≫ a = t ≫ g₂.i := by
  obtain ⟨hN, -, -, hC⟩ := hR
  have := EndTorus.connectedSpace_thickening I e
  have := g₂.q_hom
  have := g₁.i_hom
  have := g₂.i_hom
  have hk := g₂.isKernel
  have : IsProper D₂.P.A.hom := D₂.P.isAb.proper
  have hB : IsAbelianScheme (thickObj R I e D₂.P.A) :=
    { comm := inferInstance
      smooth := by have := D₂.P.isAb.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := D₂.P.isAb.geomConnected
        show GeometricallyConnected (pullback.snd _ _)
        infer_instance }
  have h1 : g₁.i ≫ a ≫ g₂.q = toUnit _ ≫ η[thickObj R I e D₂.P.A] :=
    (splitTorus_hom_abelian_eq_one _ D₁.X _ hB (g₁.i ≫ a ≫ g₂.q) inferInstance).trans (Hom.one_def)
  have : Mono g₂.i := by
    have : Mono (η[thickObj R I e D₂.P.A]) := ⟨fun _ _ _ => toUnit_unique _ _⟩
    exact (MorphismProperty.monomorphisms _).of_isPullback hk.flip (.infer_property _)
  let t := hk.lift (g₁.i ≫ a) (toUnit _) (by rw [Category.assoc, h1])
  have ht : t ≫ g₂.i = g₁.i ≫ a := hk.lift_fst _ _ _
  have : IsMonHom (t ≫ g₂.i) := ht ▸ inferInstance
  have : IsMonHom t := EndTorus.isMonHom_of_mono t g₂.i
  obtain ⟨h, hh⟩ := SplitTorusHom.exists_addMonoidHom t
  exact ⟨h, t, (torusHomOf_iff_appTop _ _).2 hh, ht.symm⟩

end GlobalTheory.Mum.Two.HomConst


open GlobalTheory.Mum.Two.HomConst in
theorem GlobalTheory.Mum.Two.unifPre_hom_character_const : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂), IsMonHom a → ∃ h : D₂.toPre.X →+ D₁.toPre.X, OnTorus U₁ U₂ a h := by
  intro R _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a ha
  have ex := fun e => exists_torus_hom hR (U₁.gt e) (U₂.gt e) ((Over.pullback (thick R I e)).map a)
  choose h t ht hi using ex
  obtain ⟨-, -, -, hC⟩ := hR
  have down : ∀ (e : ℕ) (f : D₂.toPre.X → D₁.toPre.X),
      Acts (U₁.gt e) (U₂.gt e) ((Over.pullback (thick R I e)).map a).left f →
      Acts (U₁.gt 0) (U₂.gt 0) ((Over.pullback (thick R I 0)).map a).left f := by
    intro e f
    induction e with
    | zero => exact id
    | succ e ih => exact fun k => ih (acts_down U₁ U₂ a k)
  refine ⟨h 0, fun e => ⟨t e, ?_, hi e⟩⟩
  rw [← acts_unique _ _ (down e _ (acts_of_torusHomOf _ _ _ (ht e) (hi e)))
    (acts_of_torusHomOf _ _ _ (ht 0) (hi 0))]
  exact ht e
end
end

section

open Filter Topology
open scoped SchwartzMap Uniformity

namespace GlobalTheory

theorem schwartz_family_uniform_bound : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (I : Type)
    (lam : I → SchwartzMap V ℂ →L[ℂ] ℂ) (w : I → ℝ), (∀ i, 0 ≤ w i) →
    (∀ f, ∃ (N : ℕ) (C : ℝ), ∀ i, ‖lam i f‖ ≤ C * w i ^ N) →
    ∃ (N : ℕ) (C : ℝ) (T : Finset (ℕ × ℕ)), ∀ i f,
      ‖lam i f‖ ≤ C * (T.sup (schwartzSeminormFamily ℂ V ℂ)) f * w i ^ N := by
  intro V _ _ _ I lam w hw hb
  haveI : (𝓤 𝓢(V, ℂ)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  haveI : CompleteSpace 𝓢(V, ℂ) := SchwartzComplete.completeSpace
  haveI : BaireSpace 𝓢(V, ℂ) := inferInstance
  let S : ℕ × ℕ → Set 𝓢(V, ℂ) := fun p => {f | ∀ i, ‖lam i f‖ ≤ (p.2 : ℝ) * w i ^ p.1}
  have hS : ∀ p, IsClosed (S p) := by
    intro p
    simp only [S, Set.setOf_forall]
    exact isClosed_iInter fun i =>
      isClosed_le (continuous_norm.comp (lam i).continuous) continuous_const
  have hU : ⋃ p, S p = Set.univ := by
    refine Set.eq_univ_of_forall fun f => ?_
    obtain ⟨N, C, hC⟩ := hb f
    obtain ⟨M, hM⟩ := exists_nat_ge C
    exact Set.mem_iUnion.2 ⟨(N, M), fun i =>
      (hC i).trans (mul_le_mul_of_nonneg_right hM (pow_nonneg (hw i) _))⟩
  obtain ⟨p, f₀, hf₀⟩ := nonempty_interior_of_iUnion_of_closed hS hU
  have hn : interior (S p) ∈ 𝓝 f₀ := isOpen_interior.mem_nhds hf₀
  have hn' : (fun g => f₀ + g) ⁻¹' interior (S p) ∈ 𝓝 (0 : 𝓢(V, ℂ)) := by
    have h : Tendsto (fun g : 𝓢(V, ℂ) => f₀ + g) (𝓝 0) (𝓝 f₀) := by
      simpa using (continuous_const_add f₀).tendsto 0
    exact h hn
  obtain ⟨⟨T, ε⟩, hε, hT⟩ := ((schwartz_withSeminorms ℂ V ℂ).hasBasis_zero_ball).mem_iff.1 hn'
  simp only at hε hT
  set q := T.sup (schwartzSeminormFamily ℂ V ℂ) with hq
  have hball : ∀ g, q g < ε → ∀ i, ‖lam i g‖ ≤ 2 * (p.2 : ℝ) * w i ^ p.1 := by
    intro g hg i
    have h1 : f₀ + g ∈ S p := interior_subset (hT (by simpa [Seminorm.mem_ball] using hg))
    have h2 : f₀ ∈ S p := interior_subset hf₀
    have h3 : lam i g = lam i (f₀ + g) - lam i f₀ := by simp
    rw [h3]
    calc ‖lam i (f₀ + g) - lam i f₀‖ ≤ ‖lam i (f₀ + g)‖ + ‖lam i f₀‖ := norm_sub_le _ _
      _ ≤ (p.2 : ℝ) * w i ^ p.1 + (p.2 : ℝ) * w i ^ p.1 := add_le_add (h1 i) (h2 i)
      _ = 2 * (p.2 : ℝ) * w i ^ p.1 := by ring
  refine ⟨p.1, 2 * (p.2 : ℝ) / ε, T, fun i f => ?_⟩
  set A := 2 * (p.2 : ℝ) * w i ^ p.1 / ε with hA
  have hA0 : 0 ≤ A := by
    have := pow_nonneg (hw i) p.1
    positivity
  have hq0 : 0 ≤ q f := apply_nonneg _ _
  have hscale : ∀ t, q f < t → ‖lam i f‖ ≤ t * A := by
    intro t ht
    have htpos : 0 < t := lt_of_le_of_lt hq0 ht
    have hc : ‖((ε / t : ℝ) : ℂ)‖ = ε / t := by
      rw [Complex.norm_real, Real.norm_of_nonneg (div_pos hε htpos).le]
    have hg : q (((ε / t : ℝ) : ℂ) • f) < ε := by
      rw [map_smul_eq_mul, hc]
      calc ε / t * q f < ε / t * t := mul_lt_mul_of_pos_left ht (div_pos hε htpos)
        _ = ε := by field_simp
    have h := hball _ hg i
    rw [map_smul, norm_smul, hc] at h
    rw [hA, show t * (2 * (p.2 : ℝ) * w i ^ p.1 / ε) = (t / ε) * (2 * (p.2 : ℝ) * w i ^ p.1) by ring]
    have : ‖lam i f‖ = (t / ε) * (ε / t * ‖lam i f‖) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left h (div_pos htpos hε).le
  have hfin : ‖lam i f‖ ≤ q f * A := by
    rcases hA0.lt_or_eq with hApos | hAz
    · refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
      have : q f < a / A := (lt_div_iff₀ hApos).2 ha
      calc ‖lam i f‖ ≤ a / A * A := hscale _ this
        _ = a := by field_simp
    · rw [← hAz, mul_zero]
      have := hscale (q f + 1) (by linarith)
      rwa [← hAz, mul_zero] at this
  calc ‖lam i f‖ ≤ q f * A := hfin
    _ = 2 * (p.2 : ℝ) / ε * q f * w i ^ p.1 := by rw [hA]; ring

end GlobalTheory
end
