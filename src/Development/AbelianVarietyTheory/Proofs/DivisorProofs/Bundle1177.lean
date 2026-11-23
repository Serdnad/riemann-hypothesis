module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyMulRight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle479
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1144
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1147
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

namespace GlobalTheory.CharKer

theorem isAdditive_of_isEquivGen : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' N T : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ) (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), IsAbelianScheme A → IsAbelianScheme A' → IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → M.IsLB → IsEquivGen i q χ M e → IsAdditive M := by
  intro K _ _ A A' N T _ _ _ i q χ M e hA hA' hi hq hfin hflat hsurj hker hχ hM he
  haveI := hA
  haveI := hq
  haveI : IsCommMonObj A := IsAbelianScheme.comm
  obtain ⟨h₁, h₂, h₃⟩ := GlobalTheory.T.prodMapPairTimesIdentity_flat_surjective_affine _ A A' T q hflat hsurj inferInstance
  exact isAdditive_of_universal hM (GlobalTheory.T.lineBundle_trivial_of_invariant_pullback_generator _ _ (pmap2 q T).left h₁ h₂ h₃ (addBundle M) (addGen q M e)
    (GlobalTheory.T.isPullbackLineBundleGenerator_additivityDefect _ A A' T q M e he.1) (GlobalTheory.T.additivityDefect_generator_invariant_same_image _ A A' N T i q χ M e hi hker hχ he))

end GlobalTheory.CharKer
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.PartDims

section Lin

theorem finrank_comap {X : Type} [AddCommGroup X] [Module ℂ X] {M : HMod X} {V U : Submodule ℂ X} {ip : X → X → ℂ}
    (h : M.Is V ip) (hU : U ≤ V) : Module.finrank ℂ (U.comap M.e) = Module.finrank ℂ U ∧ FiniteDimensional ℂ U := by
  have e : U.comap M.e ≃ₗ[ℂ] U :=
    (Submodule.equivMapOfInjective M.e h.1 (U.comap M.e)).trans
      (LinearEquiv.ofEq _ _ (Submodule.map_comap_eq_self (h.2.1.symm ▸ hU)))
  exact ⟨e.finrank_eq, e.finiteDimensional⟩

theorem homInto_comp {H H' S X : Type} [Group H] [Group H'] [AddCommGroup S] [Module ℂ S] [AddCommGroup X] [Module ℂ X]
    (σ : Representation ℂ H S) (ρ : Representation ℂ H' X) (C : Submodule ℂ X) (Φ : H ≃* H') :
    homInto σ (ρ.comp Φ.toMonoidHom : Representation ℂ H X) C =
      homInto (σ.comp Φ.symm.toMonoidHom : Representation ℂ H' S) ρ C := by
  ext f
  refine and_congr_right fun _ => ⟨fun h g s => ?_, fun h g s => ?_⟩
  · have := h (Φ.symm g) s
    simpa using this
  · have := h (Φ g) s
    simpa using this

end Lin

variable {D : D7}

section Level

variable {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem levChi_flag (hs : L.s = 0) (hQ : L.Q = ∅) (κ : GA D V) : levChi V β (flagL L) κ = 1 := by
  have h2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) (finE V κ)) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi levFn
  rw [h2]
  simp [flagL, withP, hs, hQ]

theorem levChi_withP (hs : L.s = 0) (hQ : L.Q = ∅) (P : LevelP L.Pg L.r ℂ) (κ : GA D V) :
    levChi V β (withP L P) κ = ((ext1 P.H P.chi (rTup β L (finE V κ)) : ℂˣ) : ℂ) := by
  have h := levChi_flag (β := β) hs hQ κ
  unfold levChi at h ⊢
  rw [levFn_withP, Units.val_mul, h, mul_one]

theorem mem_levi_flag_of_mem_parabolic (hs : L.s = 0) (hQ : L.Q = ∅) (P : LevelP L.Pg L.r ℂ) {κ : GA D V} (hκ : κ ∈ levG V β (flag1L L)) :
    κ ∈ levG V β (withP L P) ∧ levChi V β (withP L P) κ = 1 ∧ levChi V β (flag1L L) κ = 1 := by
  have h1 : rTup β L (finE V κ) = 1 := Subgroup.mem_bot.1 hκ.2.2
  refine ⟨⟨hκ.1, hκ.2.1, ?_⟩, ?_, ?_⟩
  · show rTup β L (finE V κ) ∈ P.H
    rw [h1]; exact P.H.one_mem
  · rw [levChi_withP hs hQ, h1, blockDiagonalExtendByOnePrimeField_one]; rfl
  · have h := levChi_flag (β := β) hs hQ κ
    unfold levChi at h ⊢
    rw [levFn_flag1, h]

theorem mult_le {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S)
    {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} (h : ∀ k ∈ J', k ∈ J ∧ χ k = χ' k) : Mult θ M J χ ≤ Mult θ M J' χ' := by
  refine Submodule.span_mono fun T hT => ⟨hT.aut, hT.cusp, fun v k hk g => ?_, hT.equiv, hT.cont⟩
  rw [← (h k hk).2]
  exact hT.lev v k (h k hk).1 g

theorem goodPart_le_flag {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (hs : L.s = 0) (hQ : L.Q = ∅) (P : LevelP L.Pg L.r ℂ) (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) :
    goodPart θ M (levS V β (withP L P)) (levChi V β (withP L P)) e ≤
      goodPart θ M (levS V β (flag1L L)) (levChi V β (flag1L L)) e :=
  inf_le_inf_right _ (mult_le θ M fun k hk => by
    obtain ⟨h1, h2, h3⟩ := mem_levi_flag_of_mem_parabolic hs hQ P hk
    exact ⟨h1, h2.trans h3.symm⟩)

variable {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ)

theorem gaL_star (hs : L.s = 0) (hQ : L.Q = ∅) (hc : ∀ g, star (c g) = c g) (φ : GA D V → ℂ) :
    gaL V β L eG c (star φ) = star (gaL V β L eG c φ) := by
  funext h
  have h1 : ∀ g, actG0 V β L (eG g) (star φ) h = star (actG0 V β L (eG g) φ h) := by
    intro g
    unfold actG0
    split_ifs with hk
    · simp [levChi_flag hs hQ]
    · simp
  simp only [gaL, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, Pi.star_apply, star_sum,
    smul_eq_mul, star_mul', hc]
  exact Finset.sum_congr rfl fun g _ => congrArg _ (h1 g)

variable {eG c} {P : LevelP L.Pg L.r ℂ} {Pl0 : Type} {ok : Set Pl0} {pl : Pl0 → Pl D.host.E} {q : Pl0 → ℕ} {Sg : Pl0 → ℂ[X]}
  {X : Type} [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ (GfC V) X}

theorem fixed_of_killed (hs : L.s = 0) (hQ : L.Q = ∅) {x : X} (hx : x ∈ killed ρ (eqSet V β L eG c P ok pl q Sg))
    {k : GfC V} (hk : (k : GA D V) ∈ levG V β (flag1L L)) : ρ k x = x := by
  obtain ⟨h1, h2, -⟩ := mem_levi_flag_of_mem_parabolic hs hQ P hk
  have := mem_killed.1 hx _ (Or.inl (Or.inl ⟨k, h1, rfl⟩))
  simpa [h2, sub_eq_zero] using this

theorem isTopologicalGroup_GA (V : HSp D) : IsTopologicalGroup (GA D V) := by
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  exact inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))

theorem isOpen_stab (hs : L.s = 0) (hQ : L.Q = ∅) {x : X} (hx : x ∈ killed ρ (eqSet V β L eG c P ok pl q Sg)) :
    IsOpen {g : GfC V | ρ g x = x} := by
  first
  | (rename_i h_5 h_6 h_16 h_17; revert D V β L G h_5 h_6 eG c P Pl0 ok pl q Sg X h_16 h_17 ρ hs hQ x hx; exact @_root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser)
  | exact @_root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser
  | exact _root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser
  | (apply _root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser ..)

theorem isGoodRep_of_killed (hs : L.s = 0) (hQ : L.Q = ∅) (hl : LiftsExist V β L)
    (h : killed ρ (eqSet V β L eG c P ok pl q Sg) ≠ ⊥) : IsGoodRep V β L eG c ρ := by
  obtain ⟨x, hx, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  choose κ hκ using fun g => hl (eG g)
  refine ⟨x, h0, fun k hk => fixed_of_killed hs hQ hx hk, fun g => ⟨κ g, (hκ g).1⟩, hκ, ?_⟩
  have := mem_killed.1 hx _ (Or.inl (Or.inr ⟨fun g => ⟨κ g, (hκ g).1⟩, hκ, rfl⟩))

  simpa [sub_eq_zero, map_sum, LinearMap.sum_apply] using this

end Level

section Hecke

variable {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Subgroup (GA D V)} {Pl0 : Type} {ok : Set Pl0}
  {pl : Pl0 → Pl D.host.E} {q : Pl0 → ℕ}

theorem mem_hPart {Sg : Pl0 → ℂ[X]} {x : MMap M} : x ∈ hPart M J ok pl q Sg ↔
    ∀ P ∈ ok, ∀ k ≤ V.rank, ∀ α R, IsHeckeAt V (pl P) k α → Bridge.IsDC J α⁻¹ R →
      heckeOn M R x = ((Sg P).coeff k / ((-1) ^ k * (q P : ℂ) ^ (k * (k - 1) / 2))) • x := by
  simp only [hPart, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]
  exact ⟨fun h P hP k hk α R ha hR => h P hP k hk α ha R hR, fun h P hP k hk α ha R hR => h P hP k hk α R ha hR⟩

theorem exists_conjModel {S' : D.what₂.Tau → SPar} (h : ∀ τ, S' τ = dualPar (S τ)) (M : DSModel V S) :
    ∃ (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ),
      ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w) := by
  obtain rfl : S' = fun τ => dualPar (S τ) := funext h
  exact GlobalTheory.T.discrete_series_model_of_dual_parameter M

end Hecke

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem rank_zeroth_component_eq : (Yc D 0).rank = D.R.r := by
  rw [D.sp.Y_rank _ (min_le_right _ _), Nat.zero_min]
  simp [Ranks.rankY]

theorem rank_weight_component_eq (i : Fin D.R.m) : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2

theorem sign_at_base_place_eq_embedding (R : RealDat D A Ks) : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0

theorem star_levChi (b : Bool) {κ : GA D (Yc D 0)} (hκ : κ ∈ levS _ (R.βY 0) (R.dat0 (R.levR F b))) :
    levChi _ (R.βY 0) (R.dat0 (R.levL F b D.what₂.embLL)) κ = star (levChi _ (R.βY 0) (R.dat0 (R.levR F b)) κ) := by
  have hm : rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) κ) ∈ (R.levR F b).H := hκ.2.2
  have h1 := levChi_withP (β := R.βY 0) (L := R.dat0 R.triv) rfl rfl (R.levL F b D.what₂.embLL) κ
  have h2 := levChi_withP (β := R.βY 0) (L := R.dat0 R.triv) rfl rfl (R.levR F b) κ
  replace h2 := h2.trans (congrArg Units.val (extendOne_of_mem (P := (R.levR F b).H) (R.levR F b).chi hm))
  replace h1 := h1.trans (congrArg Units.val (extendOne_of_mem (P := (R.levL F b D.what₂.embLL).H) (R.levL F b D.what₂.embLL).chi hm))
  refine h1.trans (Eq.trans ?_ (congrArg star h2).symm)
  have h3 : (R.levL F b D.what₂.embLL).chi ⟨_, hm⟩ = ((R.levR F b).chi ⟨_, hm⟩)⁻¹ := by
    exact map_inv (Units.map D.what₂.embLL.toMonoidHom) _
  have h4 : IsOfFinOrder ((R.levR F b).chi ⟨_, hm⟩) := by
    have : Finite (G0 R.Pg D.R.r) := Finite.of_equiv _ R.eG.toEquiv
    exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
  have h5 : ‖(((R.levR F b).chi ⟨_, hm⟩ : ℂˣ) : ℂ)‖ = 1 := ((Units.coeHom ℂ).isOfFinOrder h4).norm_eq_one
  rw [h3, Units.val_inv_eq_inv_val, Complex.inv_eq_conj h5]
  rfl

end GlobalTheory.PartDims

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.hInv_of_directed_union_subalgebras : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (S : ι → Subalgebra ℤ A), Monotone S → (∀ a, ∃ i, a ∈ S i) → (∀ i, IsUnit (q : S i)) → (∀ i, HInv q (S i)) → HInv q A := by
  first | (exact @GlobalTheory.EtC.hInv_of_directed_union) | (exact GlobalTheory.EtC.hInv_of_directed_union) | (intros; apply GlobalTheory.EtC.hInv_of_directed_union  <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
open scoped TensorProduct Topology

namespace GlobalTheory.HeckeSplitGen

theorem integralFiniteAdelesTensor_eq_adelicCompletion_integers (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    intAEF F E = GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
  unfold intAEF GlobalTheory.AdLat.hat1
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, rfl⟩
    exact ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
    exact ⟨a, ha, x, rfl⟩

theorem char_trivial_modSetF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ν : (AF F ⊗[F] E)ˣ →* Circle), Continuous ν →
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ GlobalTheory.HeckeSplitGen.modSetF F E N, ν x = 1 := by
  intro F E _ _ _ _ _ ν hν
  obtain ⟨e, he, -, he'⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (GlobalTheory.AdLat.RA F E) := ⟨rfl⟩
  haveI : ContinuousAdd (GlobalTheory.AdLat.RA F E) :=
    IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) _
  have hsmall := (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat F E 0 ⊤ (by simp)).2
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.finite_order_of_small (infPartF F E) (finPartF F E) e.symm he'
    (fun z => by
      rw [RingEquiv.symm_apply_eq]
      exact Prod.ext (he z).1.symm (he z).2.symm)
    (GlobalTheory.CharFin.hatRing F E) hsmall (GlobalTheory.CharFin.finite_quotient_hatRing F E) ν hν
  refine ⟨N, hN, fun x hx => ?_⟩
  obtain ⟨h1, ⟨r, hr, hxr⟩, h3⟩ := hx
  rw [integralFiniteAdelesTensor_eq_adelicCompletion_integers] at hr h3
  have hNr : (N : Af F ⊗[F] E) * r = N • r := (nsmul_eq_mul _ _).symm
  have hfin : finPartF F E (x : AEF F E) ∈ GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
    have : finPartF F E (x : AEF F E) = 1 + N • r := by rw [← hNr, ← hxr]; ring
    rw [this]
    exact add_mem (AddSubgroup.subset_closure ⟨1, fun w => one_mem _, _, ⟨1, rfl⟩,
      by simp [Algebra.TensorProduct.one_def]⟩) (nsmul_mem hr N)
  exact hker x ⟨h1, hfin, h3⟩ ⟨r, hr, by rw [hxr, hNr]⟩

end GlobalTheory.HeckeSplitGen
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.CutProd

open GlobalTheory.JSW.Cut

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

theorem lr_loc_of_mem_mirS {S : Finset (HeightOneSpectrum (𝓞 E))} {p : GA E (m + 1)} (hp : p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m))
    (w : HeightOneSpectrum (𝓞 E)) :
    GlobalTheory.JSW.KirFin.lr (GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p) = GlobalTheory.JSW.KirFin.lr 1 := by
  funext j
  have h := hp.2 j
  simp only [GlobalTheory.JSW.KirFin.lr]
  show ((pLoc E w).comp (pFin E)) ((p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j) = _
  rw [h]
  split_ifs with hj <;> simp [hj, Matrix.one_apply, eq_comm]

theorem exists_cut_prod (ψ : ∀ w : HeightOneSpectrum (𝓞 E), AddChar (w.adicCompletion E) ℂ)
    (hψ : ∀ w x, ψ w x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) (K : Subgroup (GL (Fin (m + 1)) (Af E)))
    (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E)))
    (z : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)) (S : Finset (HeightOneSpectrum (𝓞 E))) :
    (∀ w ∈ S, ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) →
    (∀ w ∈ S, Cuts (ψ w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))
      (cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1}) →
    ∃ T : GA E (m + 1) →₀ ℂ, (∀ h ∈ T.support, h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S ∧ GeneralLinearGroup.map (pInf E) h = 1) ∧
      ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) →
        (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) →
        ∀ y : GA E (m + 1), (∀ w ∈ S, GlobalTheory.JSW.KirFin.lr (GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y) =
          GlobalTheory.JSW.KirFin.lr 1) →
        GlobalTheory.JSW.Cut.act T W y = {x : GA E (m + 1) | ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈
          cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}.indicator W y := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro _ _
    refine ⟨Finsupp.single 1 1, fun h hh => ?_, fun W _ _ y _ => ?_⟩
    · have h1 : h = 1 := Finset.mem_singleton.1 (Finsupp.support_single_subset hh)
      subst h1
      exact ⟨fun v _ => map_one _, map_one _⟩
    · simp
  | insert w S hw ih =>
    intro hK hC
    obtain ⟨T₁, hT₁s, hT₁⟩ := ih (fun v hv => hK v (Finset.mem_insert_of_mem hv))
      (fun v hv => hC v (Finset.mem_insert_of_mem hv))
    obtain ⟨T₂, hT₂s, hT₂⟩ := GlobalTheory.T.localCutOperator_transfer_adelicWhittaker E m w (ψ w) (hψ w) K (U w) (hK w (Finset.mem_insert_self _ _))
      (cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1}
      (hC w (Finset.mem_insert_self _ _))
    refine ⟨comp T₁ T₂, fun k hk => ?_, fun W hN hKW y hy => ?_⟩
    · obtain ⟨a, ha, b, hb, rfl⟩ := mem_support_comp hk
      obtain ⟨g, rfl⟩ := hT₂s b hb
      have hb' := (GlobalTheory.JSW.WhitModel.loc_mem_supS (insert w S) w g).2 (Or.inl (Finset.mem_insert_self _ _))
      refine ⟨fun v hv => ?_, ?_⟩
      · rw [map_mul, (hT₁s a ha).1 v (fun h => hv (Finset.mem_insert_of_mem h)), hb' v hv, one_mul]
      · rw [map_mul, (hT₁s a ha).2, pInf_finGL, one_mul]
    · have hyh : ∀ h ∈ T₁.support, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (y * h) =
          GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y := fun h hh => by
        rw [map_mul, (hT₁s h hh).1 w hw, mul_one]
      have hyS := hT₁ W hN hKW y (fun v hv => hy v (Finset.mem_insert_of_mem hv))
      have hyw := hy w (Finset.mem_insert_self _ _)
      rw [act_comp]
      by_cases hyc : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y ∈
          cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))
      · rw [act_congr T₁ (f' := W) fun k hk => ?_, hyS]
        · simp only [Set.indicator, Set.mem_setOf_eq, Finset.forall_mem_insert, hyc, true_and]
        · rw [hT₂ W hN hKW (y * k) (by rw [hyh k hk]; exact hyw), Set.indicator_of_mem]
          rw [Set.mem_setOf_eq, hyh k hk]; exact hyc
      · rw [act_congr T₁ (f' := 0) fun k hk => ?_]
        · simp only [Set.indicator, Set.mem_setOf_eq, Finset.forall_mem_insert, hyc, false_and, if_false]
          unfold GlobalTheory.JSW.Cut.act; simp
        · rw [hT₂ W hN hKW (y * k) (by rw [hyh k hk]; exact hyw), Set.indicator_of_notMem]
          · rfl
          · rw [Set.mem_setOf_eq, hyh k hk]; exact hyc

end GlobalTheory.JSW.CutProd

theorem _root_.GlobalTheory.JSW.CutProd.cut_prod_mirS : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (ψ : ∀ w : HeightOneSpectrum (𝓞 E), AddChar (w.adicCompletion E) ℂ), (∀ w x, ψ w x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) → ∀ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))) (z : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)), (∀ w ∈ S, ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) → (∀ w ∈ S, GlobalTheory.JSW.Cut.Cuts (ψ w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) (GlobalTheory.JSW.Cut.cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1}) → ∃ T : GA E (m + 1) →₀ ℂ, (∀ h ∈ T.support, h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S ∧ GeneralLinearGroup.map (pInf E) h = 1) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.Cut.act T W p = {x : GA E (m + 1) | ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈ GlobalTheory.JSW.Cut.cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}.indicator W p := by
  intro E _ _ _ m S ψ hψ K U z hK hC
  obtain ⟨T, hTs, hT⟩ := GlobalTheory.JSW.CutProd.exists_cut_prod ψ hψ K U z S hK hC
  exact ⟨T, hTs, fun W hN hKW p hp => hT W hN hKW p fun w _ => GlobalTheory.JSW.CutProd.lr_loc_of_mem_mirS hp w⟩
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PDivGroup

theorem omega_baseChange_bijective_of_isNilpotent : ∀ (p : ℕ) [Fact p.Prime] (R R' : Type) [CommRing R]
    [CommRing R'] [Algebra R R'], IsNilpotent (p : R) → ∀ G : PDivGroup p R,
    Function.Bijective (PDiv.liftSemi (G.toBase R').omega) := by
  intro p _ R R' _ _ _ hnil G
  obtain ⟨N, hN⟩ := hnil
  have hN' : (p : R') ^ N = 0 := by
    rw [← map_natCast (algebraMap R R'), ← map_pow, hN, map_zero]
  have hL := omegaLevel_bijective_of_pow_eq_zero p R N hN G N le_rfl
  have hL' := omegaLevel_bijective_of_pow_eq_zero p R' N hN' (G.baseChange R') N le_rfl
  have hg := PDiv.liftSemi_toBaseChange_cot_bijective R R' (G.A N)
  let e : R' ⊗[R] G.omega ≃ₗ[R'] R' ⊗[R] Cot R (G.A N) :=
    LinearEquiv.baseChange R R' _ _ (LinearEquiv.ofBijective (G.omegaLevel N) hL)
  have hcomp : ((G.baseChange R').omegaLevel N).comp (PDiv.liftSemi (G.toBase R').omega) =
      (PDiv.liftSemi (toBaseChange R R' (G.A N)).cot).comp e.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, PDiv.liftSemi_tmul, map_smul, e,
      LinearEquiv.baseChange_tmul, LinearEquiv.ofBijective_apply]
    rfl
  refine Function.Bijective.of_comp_left ?_ hL'.injective
  change Function.Bijective (((G.baseChange R').omegaLevel N).comp (PDiv.liftSemi (G.toBase R').omega))
  rw [hcomp]
  exact hg.comp e.bijective

end GlobalTheory.PDivGroup
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

theorem _root_.GlobalTheory.T.homomorphism_matrix_unique_fixed_pullback : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c c' : Fin mA → Fin mB → Γ(Sp R, ⊤)), IsTest A B L M t A' B' φA' φB' Φ' → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c' → c = c' := by
  first | exact @GlobalTheory.HomFixUniq.mat_unique | exact GlobalTheory.HomFixUniq.mat_unique | (intros; apply GlobalTheory.HomFixUniq.mat_unique <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_descentDatum_additive_lineBundle_isogeny : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → P.IsLB → IsAdditive P → Triv (ev P (𝟙 A) (1 : A ⟶ B)) → (∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ q = 1 → Triv (ev P (fst T B ≫ x) (snd T B))) → ∃ φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, GlobalTheory.LBDescent.chart (q ▷ B).left P i j)ˣ, GlobalTheory.LBDescent.DescCompat (q ▷ B).left P φ ∧ GlobalTheory.LBDescent.DescCocycle (q ▷ B).left P φ := by
  first | exact @GlobalTheory.DescNorm.descentDatum_of_additive | exact GlobalTheory.DescNorm.descentDatum_of_additive | (intros; apply GlobalTheory.DescNorm.descentDatum_of_additive <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.lbIso_lbPow_sq_pull_sq2_of_isGen_of_relAmple : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ n : ℕ, LBIso (GlobalTheory.UPel.HT.Hecke.lbPow P (n ^ 2)) (P.pull (GlobalTheory.UPel.HT.Hecke.sq2 ((𝟙 A) ^ n))) := by
  exact @GlobalTheory.BirigidPow.birigidified_pullback_mulPair_iso_tensorPowSq
end
