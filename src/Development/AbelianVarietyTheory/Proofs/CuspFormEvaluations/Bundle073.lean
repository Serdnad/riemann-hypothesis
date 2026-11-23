module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormVanishingLowCoeffMemLeadingAddDeepSpan
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle026
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle037
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsUUOver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle072
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle014
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle051
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle016
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModuliUnivEtaKilled
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeviLogThetaSum
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem _root_.GlobalTheory.T.cuspForm_vanishing_low_coeff_mem_leading_add_deep_span : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → ∀ (CR c : ℝ), c1 = WeightFamilies.c1 D CR Tn c j → (∀ F ∈ WeightFamilies.MggK (recB h.toLawsCore) CR Tn c j (addL wF wL Tn), ∀ k : (T.U j T.σ₀).Comp, rdR h j F k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j (addL wF wL Tn) k) c1) → ∀ (m : ℕ) (θ : Fin m → R.Y → ℂ), (∀ i, θ i ∈ R.sp wF Set.univ) → Submodule.span ℂ (Set.range (vals xs θ)) = ⊤ → R.sp (addL wF wL Tn) (WeightFamilies.MggK n.base CR Tn c j (addL wF wL Tn)) ≤ Submodule.span ℂ (Set.range (R.lead w t Tn (a0 D j Tn) θ)) ⊔ R.deep w t ((recPlusN h j hj n).wF0 wL wF) (a0 D j Tn) := by
  first | exact @GlobalTheory.Containment.main | exact GlobalTheory.Containment.main | (intros; apply GlobalTheory.Containment.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_framedPoint_baseChange_algHom : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T) (y : FrPt Xo c S), ∃ z : FrPt Xo c T, FrMap ψ y z := by
  first | exact @GlobalTheory.FramedBaseChange.exists_frMap | exact GlobalTheory.FramedBaseChange.exists_frMap | (intros; apply GlobalTheory.FramedBaseChange.exists_frMap <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finite_levQ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (l : Level H) :
    Finite (LevQ Dw l) := by
  have hne : l.Mb ≠ ⊥ := by
    intro h
    have h2 := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h2
    have h3 : (l.M : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr (by have := l.three_le; omega)
    exact h3 h2
  have : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot l.Mb hne
  have : Module.Finite (𝓞 E) Dw.La := Dw.fin
  have : Module.Finite (𝓞 E ⧸ l.Mb) (LevQ Dw l) :=
    Module.Finite.of_restrictScalars_finite (𝓞 E) (𝓞 E ⧸ l.Mb) (LevQ Dw l)
  exact Module.finite_of_finite (𝓞 E ⧸ l.Mb)

theorem exists_cover_shortVal_data :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S') (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y'.x ⟶ Xo.univ.t.G)) (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y'.x ⟶ Xo.univ.t.G)) (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x))), φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧ (∀ i, InZh Xo Λ N (z i)) ∧ GeoInj Xo y'.x z ∧ (∀ q b, tp q b ^ N = levPt Xo y'.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b)) ∧ (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y'.s (z i b) (tp q b) (F q i b)) := by
  intro hL E _ _ _ H Dw l Xo c n Λ N hU hT hN S _ _ y
  have hN0 : 0 < N := hN.1.pos
  have hle : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La := le_trans hN.2.2 inf_le_left
  have hlev : ∀ {R R' : Type} [CommRing R] [CommRing R'] (x : Sp R ⟶ Xo.X) (x' : Sp R' ⟶ Xo.X)
      (h : ptO Xo x' ⟶ ptO Xo x) (a : Dw.La), h ≫ levPt Xo x a = levPt Xo x' a := by
    intro R R' _ _ x x' h a
    rw [levPt, levPt, ← Category.assoc, comp_toUnit]
  have hkill : ∀ {R : Type} [CommRing R] (x : Sp R ⟶ Xo.X) (a : Dw.La), KilledBy Xo l.Mb (levPt Xo x a) := by
    intro R _ x a b hb
    rw [levPt, Category.assoc, (moduli_univ_eta_killed hL E H Dw l Xo a).1 b hb, MonObj.comp_one]
  have hpowM : ∀ {R : Type} [CommRing R] (x : Sp R ⟶ Xo.X) (a : Dw.La), levPt Xo x a ^ l.M = 1 := by
    intro R _ x a
    rw [levPt, ← MonObj.comp_pow, (moduli_univ_eta_killed hL E H Dw l Xo a).2.2, MonObj.comp_one]
  have hpowN : ∀ {R : Type} [CommRing R] (x : Sp R ⟶ Xo.X) (a : Dw.La), levPt Xo x a ^ N = 1 := by
    intro R _ x a
    obtain ⟨k, hk⟩ := hN.2.1
    rw [hk, pow_mul, hpowM, one_pow]
  have : Finite (LevQ Dw l) := finite_levQ Dw l
  let _ : Fintype ((Fin n → LevQ Dw l) × Fin n) := Fintype.ofFinite _
  obtain ⟨B1, _, φ1, w, hφ1, hw⟩ := GlobalTheory.T.exists_faithfullyFlat_nthRoots_of_torsion hL E H Dw l Xo S y.x N l.M hN0
    (by have := l.three_le; omega) ((Fin n → LevQ Dw l) × Fin n)
    (fun j => levPt Xo y.x (levRep (j.1 j.2))) (fun j => hpowM _ _)
  have hw' : ∀ j, w j ^ N = levPt Xo (spMap φ1 ≫ y.x) (levRep (j.1 j.2)) := by
    intro j
    apply Over.OverMorphism.ext
    rw [hw j, ← hlev y.x (spMap φ1 ≫ y.x) (Over.homMk (spMap φ1) rfl), Over.comp_left]
    rfl
  have hroot := fun j => (exists_root_killedBy_pow E H Dw l Xo (ptO Xo (spMap φ1 ≫ y.x))
    (levPt Xo (spMap φ1 ≫ y.x) (levRep (j.1 j.2))) (w j) N hN0 (hkill _ _) (hw' j)).1
  choose tp1 htp1 htp1k using hroot
  obtain ⟨B2, _, φ2, z, hφ2, hz, hzg⟩ := GlobalTheory.T.exists_faithfullyFlat_split_isotropicGroup hL E H Dw l Xo B1 (spMap φ1 ≫ y.x) n Λ N hU hN0 hle
  let _ : Algebra c.F B2 := ((φ2.comp φ1).comp (algebraMap c.F S)).toAlgebra
  let φA : S →ₐ[c.F] B2 := { toRingHom := φ2.comp φ1, commutes' := fun _ => rfl }
  obtain ⟨y', hy'⟩ := FramedBaseChange.exists_frMap hL E H Dw l Xo c S B2 φA y
  have hyx : y'.x = spMap φ2 ≫ spMap φ1 ≫ y.x := by
    rw [hy'.1, ← Category.assoc, FramedBaseChange.spMap_spMap]
  let hA : ptO Xo y'.x ⟶ ptO Xo (spMap φ1 ≫ y.x) := Over.homMk (spMap φ2) hyx.symm
  let hB : ptO Xo y'.x ⟶ ptO Xo (spMap φ2 ≫ spMap φ1 ≫ y.x) :=
    Over.homMk (𝟙 _) (by rw [Category.id_comp]; exact hyx.symm)
  have hI := GlobalTheory.T.inZh_geoInj_stable_alt E H Dw l Xo n Λ N
  have hz' : ∀ i, InZh Xo Λ N (fun b => hB ≫ z i b) := fun i => hI.1 _ _ hB (z i) (hz i)
  have htpN : ∀ q b, (hA ≫ tp1 (q, b)) ^ N = levPt Xo y'.x (levRep (q b)) := by
    intro q b
    rw [← MonObj.comp_pow, htp1, hlev]
  have hUU := (exists_isVtOver_and_existsUnique_isUUOver hL E H Dw l Xo N hN.1 (ptO Xo y'.x) y'.s).2
  have hF : ∀ (q : Fin n → LevQ Dw l) (i : Fin (Λ.zCard N (Dw.p + Dw.q))) (b : Fin n), ∃ F,
      IsUUOver Xo.univ.t.G Xo.univ.t.PP N y'.s (hB ≫ z i b) (hA ≫ tp1 (q, b)) F := by
    intro q i b
    refine (hUU _ _ ((hz' i).1 b) ?_).exists
    rw [pow_two, pow_mul, htpN, hpowN]
  choose F hF using hF
  refine ⟨B2, inferInstance, inferInstance, φA, y', fun i b => hB ≫ z i b, fun q b => hA ≫ tp1 (q, b), F,
    RingHom.FaithfullyFlat.stableUnderComposition φ1 φ2 hφ1 hφ2, hy', hz', ?_, ?_, hF⟩
  · exact hI.2.2.1 B2 B2 _ y'.x (RingHom.id B2) hB
      (Spec.map_id (CommRingCat.of B2)).symm _ z hzg
  · intro q b
    obtain ⟨j, hj⟩ := htp1k (q, b)
    exact ⟨htpN q b, j, fun a ha => by rw [Category.assoc, hj a ha, MonObj.comp_one]⟩

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShortValMove

open GlobalTheory.TranslMove GlobalTheory.VVRank

section Sections

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] {φ : A.left ⟶ G.left}
  {T : Over S'} {T₀ : Over S} {L₀ : LB G.left} {L₁ : LB A.left}
  {w : LB.Iso L₁ (L₀.pull φ)} {Ψ : (T ⊗ A).left ⟶ (T₀ ⊗ G).left}

theorem secRel_of_charts (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (h₂ : Ψ ≫ (snd T₀ G).left = (snd T A).left ≫ φ)
    (s₀ : LB.Sec (LPow G L₀ 1 T₀)) (s : LB.Sec (LPow A L₁ 1 T))
    (H : ∀ (i : L₀.ι) (j : L₁.ι) (W : (T ⊗ A).left.Opens),
      W = (snd T A).left ⁻¹ᵁ ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)) →
      ∀ (h₀ : W ≤ (snd T A).left ⁻¹ᵁ ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)))
      (h₁ : W ≤ Ψ ⁻¹ᵁ (LPow G L₀ 1 T₀).U (fun _ => i)) (h₂ : W ≤ (LPow A L₁ 1 T).U (fun _ => j)),
      (Ψ.appLE ((LPow G L₀ 1 T₀).U (fun _ => i)) W h₁).hom (s₀.f (fun _ => i)) =
        ((snd T A).left.appLE ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)) W h₀).hom
          (Units.val (w.s ((fun _ => i), j))) *
        ((T ⊗ A).left.presheaf.map (homOfLE h₂).op).hom (s.f (fun _ => j))) : SecRel w Ψ s₀ s := by
  refine (secRel_iff hL₀ hL₁ h₂ 1 Nat.cast_one.symm s₀ s).2 fun i j W k₀ k₁ k₂ => fn_ext fun x hx => ?_
  have m₁ : (snd T A).left ⁻¹ᵁ ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)) ≤
      Ψ ⁻¹ᵁ (LPow G L₀ 1 T₀).U (fun _ => i) := fun p hp => Set.mem_iInter.2 fun _ => by
    have h : ((snd T A).left ≫ φ) p ∈ L₀.U i := mem_pull.1 hp.1
    rw [← h₂] at h
    exact h
  have m₂ : (snd T A).left ⁻¹ᵁ ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)) ≤
      (LPow A L₁ 1 T).U (fun _ => j) := fun p hp => Set.mem_iInter.2 fun _ => hp.2
  have e := congrArg (gs (𝟙 _) x _) (H i j _ rfl le_rfl m₁ m₂)
  have hx' : (𝟙 (T ⊗ A).left : _ ⟶ _) x ∈ W := hx
  have hx₀ := k₀ hx'
  rw [gs_mul _ _ _ hx₀, TranslMove.gs_appLE _ _ _ _ _ _ hx₀, TranslMove.gs_appLE _ _ _ _ _ _ hx₀,
    gs_res _ _ _ hx₀] at e
  rw [pow_one, gs_mul _ _ _ hx', TranslMove.gs_appLE _ _ _ _ _ _ hx', TranslMove.gs_appLE _ _ _ _ _ _ hx',
    gs_res _ _ _ hx']
  exact e

end Sections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem sv_pull {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x')}
    (ha : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i),
      (pm.appLE _ _ h).hom (s.f i) = s'.f i)
    {Z : Scheme.{0}} (r : Z ⟶ Gx x') (z : Z) {J} (hJ : Good Xo.univ.t.PP.L z J) :
    sv Xo.univ.t.G s (r ≫ pm) z J = sv Xo.univ.t.G s' r z J := by
  have hm := hJ.mem (fun _ : Fin 1 => (snd (Over.mk x') Xo.univ.t.G).left) r
  refine (sval_of s (r ≫ pm) z J (fun _ => J (r ≫ (snd (Over.mk x') Xo.univ.t.G).left))
    (fun _ => by rw [Category.assoc, hs])).trans ?_
  refine (TranslMove.gs_appLE r pm z _ _ (FramedBaseChange.chart_le pm hs _) hm _).symm.trans ?_
  exact congrArg (gs r z _) (ha _ _)

theorem exists_ptEquiv {S : Type} [CommRing S] {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ)
    {x x' : Sp S ⟶ Xo.X} (hx : x' = x ≫ ρ) :
    ∃ e : (ptO Xo x ⟶ Xo.univ.t.G) ≃* (ptO Xo x' ⟶ Xo.univ.t.G), ∀ p, (e p).left = p.left ≫ ν.φ := by
  subst hx
  refine ⟨MulEquiv.ofBijective (pushHom ν.cart (ptO Xo x)) ⟨fun p q h => ?_, fun q => ?_⟩, fun p => rfl⟩
  · exact Over.OverMorphism.ext (ν.cart.1.hom_ext (congrArg (fun t => t.left) h)
      ((Over.w p).trans (Over.w q).symm))
  · exact ⟨Over.homMk (ν.cart.1.lift q.left x (Over.w q)) (ν.cart.1.lift_snd _ _ _),
      Over.OverMorphism.ext (ν.cart.1.lift_fst _ _ _)⟩

theorem exists_move_baseChange {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} {y y' : FrPt Xo c S} (hm : FrMove ρ ν y y')
    {φ : S →ₐ[c.F] T} {z z' : FrPt Xo c T} (h : FrMap φ y z) (h' : FrMap φ y' z') :
    z'.x = z.x ≫ ρ ∧ (∀ τ i, z'.u τ i = z.u τ i ≫ ν.φ) ∧
    ∃ (pm : Gx z.x ⟶ Gx z'.x) (w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)),
      pm ≫ (fst (Over.mk z'.x) Xo.univ.t.G).left = (fst (Over.mk z.x) Xo.univ.t.G).left ∧
      pm ≫ (snd (Over.mk z'.x) Xo.univ.t.G).left = (snd (Over.mk z.x) Xo.univ.t.G).left ≫ ν.φ ∧
      CubIso ν w ∧ SecRel (T := Over.mk z.x) (T₀ := Over.mk z'.x) w pm z'.s z.s := by
  obtain ⟨hx, hu, pm, w, hf, hs, hw, hc⟩ := hm
  obtain ⟨gx, gu, p, ps, pf, pa⟩ := h
  obtain ⟨gx', gu', p', ps', pf', pa'⟩ := h'
  have hL := Xo.univ.t.PP.isLB
  have ex : z'.x = z.x ≫ ρ := by rw [gx', gx, hx, Category.assoc]
  have sq : (fst (Over.mk z.x) Xo.univ.t.G).left ≫ z'.x =
      ((snd (Over.mk z.x) Xo.univ.t.G).left ≫ ν.φ) ≫ Xo.univ.t.G.hom := by
    rw [Category.assoc, ν.cart.1.w, ex, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ ρ) ((Over.w (fst (Over.mk z.x) Xo.univ.t.G)).trans
      (Over.w (snd (Over.mk z.x) Xo.univ.t.G)).symm)
  let q : Gx z.x ⟶ Gx z'.x := pullback.lift (f := z'.x) (g := Xo.univ.t.G.hom) _ _ sq
  have qf : q ≫ (fst (Over.mk z'.x) Xo.univ.t.G).left = (fst (Over.mk z.x) Xo.univ.t.G).left :=
    pullback.lift_fst _ _ _
  have qs : q ≫ (snd (Over.mk z'.x) Xo.univ.t.G).left = (snd (Over.mk z.x) Xo.univ.t.G).left ≫ ν.φ :=
    pullback.lift_snd _ _ _
  have comm : q ≫ p' = p ≫ pm := FramedBaseChange.pulledGroup_hom_ext _ _
    (by rw [Category.assoc, ps', qs, Category.assoc, hs, ← Category.assoc, ps])
    (by rw [Category.assoc, pf', ← Category.assoc, qf, Category.assoc, hf, pf])
  have R := secRel_of_charts (T := Over.mk y.x) (T₀ := Over.mk y'.x) hL hL hs y'.s y.s hc
  refine ⟨ex, fun τ i => by rw [gu', gu, hu, Category.assoc], q, w, qf, qs, hw, fun Z r t J₀ J hJ₀ hJ => ?_⟩
  have a₁ := sv_pull p' ps' pa' (r ≫ q) t hJ₀
  have a₂ := sv_pull p ps pa r t hJ
  have a₃ := R Z (r ≫ p) t J₀ J hJ₀ hJ
  rw [Category.assoc, comm, ← Category.assoc] at a₁
  rw [Category.assoc r p (snd (Over.mk y.x) Xo.univ.t.G).left, ps] at a₃
  exact a₁.symm.trans (a₃.trans (congrArg _ a₂))

theorem eta_congr {a b : Dw.La}
    (h : (Submodule.Quotient.mk a : LevQ Dw l) = Submodule.Quotient.mk b) : Xo.univ.eta a = Xo.univ.eta b := by
  have h2 := Xo.univ.eta_add (a - b) b
  rwa [sub_add_cancel, Xo.univ.eta_ker _ ((Submodule.Quotient.eq _).1 h), _root_.one_mul] at h2

theorem mk_levRep (q : LevQ Dw l) : (Submodule.Quotient.mk (levRep q) : LevQ Dw l) = q :=
  Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)

theorem shortValAt_move : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (gM gA : Dw.La →ₗ[𝓞 E] Dw.La) (y y' : FrPt Xo c S), IsLevMove ρ ν gM gA → FrMove ρ ν y y' → ∀ σq : LevQ Dw l ≃ LevQ Dw l, (∀ a, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (gM a)) → ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ) (v : S), ShortValAt Xo c nab w Λ β N P y' v → ShortValAt Xo c nab (fun q => w (fun b => σq.symm (q b))) Λ β N P y v := by
  intro hLaw hCI E _ _ _ H Dw l Xo c _ nab hnab S _ _ ρ ν gM gA y y' hlev hmv σq hσ n a P hP w Λ β N v hv
  obtain ⟨S', _, _, φ, y₁', z', tp', F', hff, hfr, hZ, hG, htp, hUU, hval⟩ := hv
  obtain ⟨y₁, hy₁⟩ := GlobalTheory.FramedBaseChange.exists_frMap hLaw E H Dw l Xo c S S' φ y
  obtain ⟨hx, hu, pm, ω, hf, hs, hω, hR⟩ := exists_move_baseChange hmv hy₁ hfr
  have hL := Xo.univ.t.PP.isLB
  obtain ⟨e, he⟩ := exists_ptEquiv ν hx
  have he' : ∀ p, p.left = (e.symm p).left ≫ ν.φ := fun p => by rw [← he, e.apply_symm_apply]
  have hact : ∀ p b, e (p ≫ Xo.univ.t.act.act b) = e p ≫ Xo.univ.t.act.act b := fun p b =>
    Over.OverMorphism.ext (by
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc, ν.act])
  have hact' : ∀ p b, e.symm p ≫ Xo.univ.t.act.act b = e.symm (p ≫ Xo.univ.t.act.act b) := fun p b =>
    e.injective (by rw [hact, e.apply_symm_apply, e.apply_symm_apply])
  have hlv : ∀ q : LevQ Dw l, e (levPt Xo y₁.x (levRep q)) = levPt Xo y₁'.x (levRep (σq.symm q)) := fun q => by
    have h1 : Xo.univ.eta (levRep q) = Xo.univ.eta (gM (levRep (σq.symm q))) :=
      eta_congr (by rw [← hσ, mk_levRep, mk_levRep, σq.apply_symm_apply])
    refine Over.OverMorphism.ext ?_
    rw [he, levPt, levPt, h1, Over.comp_left, Over.comp_left, Category.assoc, hlev.2.1, Over.toUnit_left,
      Over.toUnit_left]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hx.symm)
  choose F hF hFF using fun (q : Fin n → LevQ Dw l) i b =>
    isUUOver_move hLaw E H Dw l Xo c S' ρ ν y₁ y₁' pm ω hx hf hs hω
      ((secRel_iff hL hL hs 1 Nat.cast_one.symm y₁'.s y₁.s).1 hR) N (e.symm (z' i b))
      (e.symm (tp' (fun b => σq.symm (q b)) b)) (z' i b) (tp' (fun b => σq.symm (q b)) b) (he' _) (he' _)
      (F' (fun b => σq.symm (q b)) i b) (hUU _ i b)
  refine ⟨S', inferInstance, inferInstance, φ, y₁, fun i b => e.symm (z' i b),
    fun q b => e.symm (tp' (fun b => σq.symm (q b)) b), F, hff, hy₁, fun i => ⟨fun b => ?_, ?_⟩, ?_,
    fun q b => ⟨?_, ?_⟩, hF, ?_⟩
  · rw [← map_pow, (hZ i).1 b, map_one]
  · intro mu hmu cm hcm k
    have h := congrArg e.symm ((hZ i).2 mu hmu cm hcm k)
    rw [map_list_prod, List.map_ofFn, map_one] at h
    simp only [hact']
    exact h
  · intro k _ ψ g hg i j hij
    refine hG k ψ (Over.homMk (spMap ψ) rfl) rfl (funext fun b => Over.OverMorphism.ext ?_)
    have h := congrArg (fun t => t.left ≫ ν.φ) (congrFun hij b)
    simp only [Over.comp_left, hg, Category.assoc, ← he'] at h
    exact h
  · rw [← map_pow, (htp _ b).1, ← hlv, e.symm_apply_apply]
  · obtain ⟨j, hj⟩ := (htp (fun b => σq.symm (q b)) b).2
    exact ⟨j, fun t ht => by rw [hact', hj t ht, map_one]⟩
  · rw [hval]
    congr 1
    refine (finsum_comp_equiv (Equiv.piCongrRight fun _ : Fin n => σq.symm)).symm.trans
      (finsum_congr fun q => ?_)
    refine congrArg₂ (· * ·) rfl (Finset.sum_congr rfl fun i _ => ?_)
    exact GlobalTheory.T.harmonic_values_invariant_universal_endomorphism hLaw hCI E H Dw l Xo c nab hnab S' ρ ν y₁ y₁' pm ω hx hf hs hω hu n a P hP N
      (F q i) (F' (fun b => σq.symm (q b)) i) (hFF q i)

end GlobalTheory.ShortValMove
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ContDiff

theorem _root_.GlobalTheory.T.log_theta_sum_invariant_smooth_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → (∃ w0 : 𝓞 E, ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) - Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) → ∀ ps : Frame X.Ψ r → ℝ, (∀ x ∈ X.dom, ∃ A : TorusAt X.toData x, ps x = Real.log (∑ᶠ (a : Fin A.T.r → Vsp A.T.dim) (_ : a ∈ {a : Fin A.T.r → Vsp A.T.dim | (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧ ∀ x ∈ A.T.L, ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}), ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s)) → IsInvFn X.toData ps ∧ ∀ x0 ∈ X.dom, ContDiffOn ℝ ∞ (fun z => ps (cpt X.toData x0 z)) {z | cpt X.toData x0 z ∈ X.dom} := by
  first | exact @GlobalTheory.ThetaLogSum.log_theta_sum_invariant_smooth | exact GlobalTheory.ThetaLogSum.log_theta_sum_invariant_smooth | (intros; apply GlobalTheory.ThetaLogSum.log_theta_sum_invariant_smooth <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ContDiff

theorem _root_.GlobalTheory.T.levi_log_theta_sum_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → (∃ w0 : 𝓞 E, ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) - Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) → ∀ ps : Frame X.Ψ r → ℝ, (∀ x ∈ X.dom, ∃ A : TorusAt X.toData x, ps x = Real.log (∑ᶠ (a : Fin A.T.r → Vsp A.T.dim) (_ : a ∈ {a : Fin A.T.r → Vsp A.T.dim | (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧ ∀ x ∈ A.T.L, ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}), ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s)) → ∀ x0 ∈ X.dom, ∀ z, cpt X.toData x0 z ∈ X.dom → ∀ ξ : Fin (nd X.toData) → ℂ, -((r : ℝ) / 2 * leviM X.toData (phla X.toData (fun _ j => if X.p0 ≤ (j : ℕ) then 1 else -1)) x0 z ξ) ≤ leviM X.toData ps x0 z ξ := by
  first | exact @GlobalTheory.ThetaSumLevi.levi_log_theta_sum | exact GlobalTheory.ThetaSumLevi.levi_log_theta_sum | (intros; apply GlobalTheory.ThetaSumLevi.levi_log_theta_sum <;> assumption)
end
