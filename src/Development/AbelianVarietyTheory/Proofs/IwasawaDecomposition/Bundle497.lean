module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle030
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle430
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle400
public import Formalism.LocalRingCardinality.Bundle003
public import Formalism.LocalToGlobal.Divisibility.ColumnFamilyPlaceCharacterComap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle143
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle155
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle144
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle051
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEvaluationMapSmoothAutomorphicValues
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.Columns.Bundle010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle386
import Formalism.LocalToGlobal.HermitianForms.Bundle007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle489
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle490
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle488
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3

theorem twArgs_lev : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L) (Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC) (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : RowsT K w Z Wt ex.p0) (a : TwArgs ex t), HEq a.x.R.C (Top.Fr.at (w.st Z) f) ∧ HEq a.x.R.Pg (B.primes w.px).vGs ∧ (∀ μ, Formalism.IndefR.RecTie.Used0 (w.st Z).toD7 μ → HEq (a.x.R.Q (a.x.Y.tupT μ)) (w.I.Q μ) ∧ HEq (a.x.R.toLevCh.xiH (a.x.Y.tupT μ)) (w.I.xi μ)) ∧ (∀ i p v s, a.x.R.EEp3 p ≠ ⊥ → ∃ p' s', HEq p' p ∧ HEq s' s ∧ a.x.R.lam3 i s p v = t.r.z.R.lam3 i s' p' v) := by
  intro K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t a
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  have hT' : Y.tupT = t.r.Y.tupT := eq_of_heq htupT
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact heq_of_eq (t.r.z.lev.C.trans (congrArg _ w.C_eq))
  · exact heq_of_eq t.r.z.lev.Pg
  · change ∀ μ, Formalism.IndefR.RecTie.Used0 (w.st Z).toD7 μ →
      HEq (t.r.z.R.Q (Y.tupT μ)) (w.I.Q μ) ∧ HEq (t.r.z.R.xiH (Y.tupT μ)) (w.I.xi μ)
    intro μ hμ
    have hix : ixOf w.I (usedOf w.I T Wt) (t.r.Y.tupT μ) = μ := (t.r.tup_ix _).symm.trans (t.r.Y.tupTie μ hμ)
    rw [hT', t.r.z.lev.Q, t.r.z.lev.xiH, hix]
    exact ⟨HEq.rfl, HEq.rfl⟩
  · intro i p v s hp
    refine ⟨p, s, HEq.rfl, HEq.rfl, ?_⟩
    change t.r.z.R.EEp3 p ≠ ⊥ at hp
    change lam i s p v = t.r.z.R.lam3 i s p v
    exact lam_eq i s p v hp


end GlobalTheory.Mem.R3
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

theorem hostPins_wpt : GlobalTheory.NT.RayField → ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K), GlobalTheory.Mem.HD.HostPins (q.w.D q.Z) q.O.ex.nch := by
  intro hR 𝒮 K q
  obtain ⟨B, f, T, w, Z, O, x⟩ := q
  have hmu := x.what₂.mu
  have key := GlobalTheory.Mem.Top.TupTieW.tupTied_of_muIsW (w.st Z) f T x.Wt w.I.xi hmu
  have hδ : w.δ.ray ≤ B.KsC := w.exact.lower.1
  have hQ : ∀ v ∈ x.Wt, O.ex.nch.Q v = T.Q v := fun v hv => (x.n.Q v hv).1
  refine ⟨fun u i => (w.D Z).T_ne_g u i, ?_, fun v hv v' hv' u => ?_, B.galLL, GlobalTheory.Mem.HD.exists_hilbert_le_O hR B w.δ hδ⟩
  · exact key.2.1.subset fun v hv => (key.1 v).1 hv
  · have hvW := (key.1 v).1 hv
    rw [hQ v hvW] at hv'
    have e : ((w.D Z).mem u).A.T = B.T u := (w.st Z).C.A_T u
    have hp : (B.T u).Prime := e ▸ ((w.D Z).mem u).A.T_prime
    rw [e]
    exact GlobalTheory.Mem.HD.twistConductor_not_over_levelPrimes B T v hv' u hp

end GlobalTheory.Mem.Top.Bl
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
  NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AmbCrd

open Formalism.L2.DIV Formalism.L2.Rows

theorem majAt_frm {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (h : PosAt H v) (x y : Fin n → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (frm H) v x y = hAt H v x y := by
  have hp := GlobalTheory.T.posDef_map_embedding_of_positiveAtPlace H v h
  rw [majAt_eq, frm_of_posDef H v hp, (frameOfSpec _ _ hp).2]
  simp only [hAt, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]

section Level

variable (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ} (A : FamIn D.what₂.LL G Pl0 T m)
  (P : Subgroup G) (ψ : P →* D.what₂.LLˣ)

theorem rNab_rdx {t1 t2 : T} (e : t1 = t2) (h : rDim D A P ψ t2 = rDim D A P ψ t1) :
    rNab D A P ψ t2 = (rNab D A P ψ t1).map ((rdx h).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := by
  subst e
  ext x
  simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, rdx_refl]
  exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, e⟩ => e ▸ hy⟩

theorem majAt_rdx {t1 t2 : T} (e : t1 = t2) (h : rDim D A P ψ t2 = rDim D A P ψ t1) (v : InfinitePlace D.what₂.LL)
    (hp : PosAt (rH D A P ψ t1) v) (x y : Fin (rDim D A P ψ t1) → D.what₂.LL) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) (frm (rH D A P ψ t2)) v (rdx h x) (rdx h y) =
      hAt (rH D A P ψ t1) v x y := by
  subst e
  have := D.tcLL
  rw [rdx_refl, rdx_refl]
  exact majAt_frm _ v hp x y

end Level

theorem tie_level (D : D7) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) {G : Type} [Group G] [Fintype G] {Pl0 T T' : Type} {m : ℕ} (A : FamIn D.what₂.LL G Pl0 T m)
    (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (tp : D.what₂.Tup → T)
    (j : ∀ μ, (Fin (rDim D A P ψ (tp μ)) → D.what₂.LL) →ₛₗ[D.what₂.embLL] S.Amb μ)
    (E : ∀ μ, Matrix (Fin (rDim D A P ψ (tp μ))) (Fin (rDim D A P ψ (tp μ))) D.what₂.LL)
    (op : ∀ μ, S.Amb μ →ₗ[ℂ] S.Amb μ)
    (hF : ∀ μ, FormsTie D.what₂.embLL (j μ) (rH D A P ψ (tp μ)) (E μ) (op μ))
    (hL : ∀ μ, OLatTie D.what₂.embLL (S.Mtilde μ) (j μ) (rNab D A P ψ (tp μ)))
    (f : T' → T) (μ0' : T') (tup : T' → D.what₂.Tup) (hf : ∀ s, f s = tp (tup s))
    (j' : ∀ s, (Fin (rDim D (A.comap f μ0') P ψ s) → D.what₂.LL) →ₛₗ[D.what₂.embLL] S.Amb (tup s))
    (hs : ∀ s, SameOn (j (tup s)) (j' s)) :
    ∃ (Fm : AmbForm D S) (J : AmbIds D (A.comap f μ0') S Fm P ψ tup), AmbTie D (A.comap f μ0') S Fm P ψ tup j' J := by
  have := D.tcLL
  let Fm : AmbForm D S :=
    { MtH := fun μ => toHLat (frm (rH D A P ψ (tp μ))) (rNab D A P ψ (tp μ))
      jAmb := j
      MtH_good := fun μ _ => ⟨frm_det _, GlobalTheory.T.fg_span_top_of_lattice_compatible_semilinear D.what₂.embLL (S.Mtilde μ) (j μ) _ (hF μ).li (hL μ)⟩
      jAmb_basis := fun μ _ => by
        show LinearIndependent ℂ (fun i => j μ (Pi.basisFun D.what₂.LL _ i)) ∧
          Submodule.span ℂ (Set.range (fun i => j μ (Pi.basisFun D.what₂.LL _ i))) = ⊤
        simp only [Pi.basisFun_apply]
        exact ⟨(hF μ).li, (hF μ).span⟩
      jAmb_lat := fun μ _ x => (hL μ).2 x
      jAmb_gen := fun μ _ => (hL μ).1
      jAmb_norm := fun μ _ x => GlobalTheory.T.normAt_standardFrame_eq_norm_complexForm D.what₂.embLL D.starLL_cx (j μ) _ _ _ (hF μ) x }
  let J : AmbIds D (A.comap f μ0') S Fm P ψ tup := ⟨fun s _ => rdx (hs s).1⟩
  refine ⟨Fm, J, ⟨fun s _ x => ?_, fun s _ => ?_, fun s _ v hv x y => ?_⟩⟩
  · refine (hs s).2 _ x fun a a' e => ?_
    show x (Fin.cast (hs s).1 a) = x a'
    congr 1
    exact Fin.ext e
  · exact rNab_rdx D A P ψ (hf s) _
  · exact majAt_rdx D A P ψ (hf s) _ v hv x y

-- Transport the dependent maps and ties along an explicit family equality.
private theorem tie_level_of_comap_eq (D : D7) {EE : Type} [NormedAddCommGroup EE]
    [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE)
    {G : Type} [Group G] [Fintype G] {Pl0 T T' : Type} {m : ℕ}
    (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ)
    (tp : D.what₂.Tup → T)
    (j : ∀ μ, (Fin (rDim D A P ψ (tp μ)) → D.what₂.LL) →ₛₗ[D.what₂.embLL] S.Amb μ)
    (E : ∀ μ, Matrix (Fin (rDim D A P ψ (tp μ))) (Fin (rDim D A P ψ (tp μ))) D.what₂.LL)
    (op : ∀ μ, S.Amb μ →ₗ[ℂ] S.Amb μ)
    (hF : ∀ μ, FormsTie D.what₂.embLL (j μ) (rH D A P ψ (tp μ)) (E μ) (op μ))
    (hL : ∀ μ, OLatTie D.what₂.embLL (S.Mtilde μ) (j μ) (rNab D A P ψ (tp μ)))
    (f : T' → T) (μ0' : T') {A' : FamIn D.what₂.LL G Pl0 T' m}
    (hA : A.comap f μ0' = A') (tup : T' → D.what₂.Tup) (hf : ∀ s, f s = tp (tup s))
    (j' : ∀ s, (Fin (rDim D A' P ψ s) → D.what₂.LL) →ₛₗ[D.what₂.embLL] S.Amb (tup s))
    (hs : ∀ s, SameOn (j (tup s)) (j' s)) :
    ∃ (Fm : AmbForm D S) (J : AmbIds D A' S Fm P ψ tup), AmbTie D A' S Fm P ψ tup j' J := by
  subst A'
  exact tie_level D S A P ψ tp j E op hF hL f μ0' tup hf j' hs

private theorem famC_comap_incl {B : Base} {px : PreX B.toPre} (I : ColIn B px)
    (hX : B.fields.Ok) {U V : Set I.ι} (Xg : Finset (R3.Gc B px → B.LL)) (tr : R3.TrI B px)
    (h : R3.tuOf I U ⊆ R3.tuOf I V) :
    (R3.famC I hX V Xg tr).A.comap (TupF.incl h) (mu0F (R3.tuOf I U)) =
      (R3.famC I hX U Xg tr).A := rfl

theorem ambEx_of_rx : ∀ 𝒮 : Slots, 𝒮.Rx = RX → AmbEx 𝒮 := by
  rintro ⟨Rx, Nx, Sx, Ox⟩ h
  dsimp only at h
  subst h
  refine StepW.of_all fun K B f T w _ _ _ => ?_
  intro Z l
  have x : RXs l.what₂ := l.rx
  have hsub : R3.tuOf w.I (R3.usedOf w.I T l.Wt) ⊆ R3.tuOf w.I Set.univ := fun τ hτ => by
    obtain ⟨a, -, e⟩ := (R3.mem_tuOf w.I).1 hτ
    exact (R3.mem_tuOf w.I).2 ⟨a, Set.mem_univ _, e⟩
  have hf : ∀ s, TupF.incl hsub s = tAll w.I (l.what₂.r.Y.tup s) := fun s => by
    apply Subtype.ext
    show s.1 = w.I.tup (l.what₂.r.Y.tup s)
    have e : l.what₂.r.Y.tup s = R3.ixOf w.I _ s := l.what₂.r.tup_ix s
    rw [e, R3.tup_ixOf]
  have hFam := famC_comap_incl w.I l.what₂.hX l.what₂.r.z.Xg l.what₂.r.z.tr hsub
  obtain ⟨a, J, hJ⟩ := tie_level_of_comap_eq (w.st Z).toD7 (RowSide.sharp _) (famAll l.what₂)
    (R3.lev1 w.I) (R3.chr1 w.I) (tAll w.I) x.all.jA _ _ x.all.formsA x.all.latA
    (TupF.incl hsub) (mu0F _) hFam l.what₂.r.Y.tup hf l.what₂.r.Y.jA x.jA_use
  obtain ⟨a0, J0, hJ0⟩ := tie_level_of_comap_eq (w.st Z).toD7 l.p0.s (famAll l.what₂)
    (R3.lev0 w.I) (R3.chr0 w.I) (tAll w.I) x.all.jA0 _ _ x.all.formsAtBottomLevel x.all.latA0
    (TupF.incl hsub) (mu0F _) hFam l.what₂.r.Y.tup hf l.what₂.r.Y.jA0
    x.movedReadingSameMaps_baseReading_agrees
  exact ⟨a, a0, ⟨J, hJ⟩, ⟨J0, hJ0⟩⟩

end GlobalTheory.AmbCrd

end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RayEv

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel

theorem formEq_term {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O D.X] {oa : D.OAct O} (Y : Ray oa) (k : ℕ) (α : D.X) :
    FormEq (Sum.elim (fun i => Y.q.left ≫ DegPre.famφB D α i) (DegPre.gtφT D Y.H Y.q α))
      (Sum.elim (DegPre.famε k) DegPre.gtε) (K' := Fin 1) (fun _ => Y.q.left) (fun _ => (k : ℤ)) := by
  have e1 : Y.q ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α) = padd D.P.A (DegPre.cT D Y.H α) Y.q := by
    simp only [padd, comp_lift_assoc, Category.comp_id]
    rw [← Hom.mul_def, ← Hom.mul_def, mul_comm, comp_toUnit_assoc]
  have e2 : Y.q.left ≫ (toUnit D.P.A ≫ D.c α).left = (DegPre.cT D Y.H α).left := by
    rw [← Over.comp_left, comp_toUnit_assoc]
  have e3 : Y.q.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (DegPre.zeroT D Y.H).left := by
    rw [← Over.comp_left, comp_toUnit_assoc]
  have e0 : Y.q.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left =
      (padd D.P.A (DegPre.cT D Y.H α) Y.q).left := by
    rw [← Over.comp_left, e1]
  intro U _ h
  rw [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four, Fin.prod_univ_one]
  simp only [Sum.elim_inl, Sum.elim_inr]
  simp only [DegPre.famφB, DegPre.famε, DegPre.gtφT, DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Category.comp_id, e0, e2, e3]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

theorem exists_sec_fourierTerm (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (Y : Ray oa) (k : ℕ) (α : D.X) (σ : D.SecB k α) : ∃ τ : LB.Sec (LB.LinComb D.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (k : ℤ)), ∀ (T : Over (Sp R)) (x : T ⟶ Y.H) y J, Good D.P.L y J → sval τ x.left y J = sval σ (x ≫ Y.q).left y J * (val ((Y.Φ T x).s α) (𝟙 _) y J).val := by
  obtain ⟨τ, hτ⟩ := exists_sec D.P.isLB (formEq_term Y k α)
    (pullMulSec σ Y.q.left ((Y.Φ Y.H (𝟙 _)).s α) ((Y.Φ Y.H (𝟙 _)).isGen α))
  refine ⟨τ, fun T x y J hJ => ?_⟩
  refine (hτ _ _ y J hJ).trans ((sval_pullMulSec σ Y.q.left ((Y.Φ Y.H (𝟙 _)).s α) ((Y.Φ Y.H (𝟙 _)).isGen α)
    x.left y hJ).trans ?_)
  obtain ⟨-, h₂⟩ := (isPull_iff _ _ _).1 (Y.rep.1 T Y.H x (𝟙 _))
  have e := h₂ α y J hJ
  rw [Category.comp_id] at e
  rw [Over.comp_left]
  exact congrArg _ (congrArg Units.val e.symm)

end GlobalTheory.RayEv
end
end

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RayEv

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

theorem smooth_gtCoord_q {H : Over (Spec (CommRingCat.of R))} [GrpObj H] [IsCommMonObj H]
    (c : GtCoord (⊥ : Ideal R) D 0 H) : Smooth c.q.left := by
  have := c.q_hom
  have := c.i_hom
  have := c.q_flat
  have := c.q_surj
  have := c.q_affine
  obtain ⟨-, -, -, -, h1, -⟩ := (GlobalTheory.splitTorus_properties (Spec (CommRingCat.of (R ⧸ (⊥ : Ideal R) ^ (0 + 1))))).1 D.X
  have : Smooth (splitTorus (Spec (CommRingCat.of (R ⧸ (⊥ : Ideal R) ^ (0 + 1)))) D.X).hom :=
    SmoothOfRelativeDimension.smooth (Module.finrank ℤ D.X) _
  have H' := (GlobalTheory.UnitRigidity.isPullback_act c.i c.q c.isKernel).map (Over.forget _)
  have a1 : Smooth (snd (splitTorus (Spec (CommRingCat.of (R ⧸ (⊥ : Ideal R) ^ (0 + 1)))) D.X)
      (thickObj R ⊥ 0 H)).left :=
    inferInstanceAs (Smooth (pullback.snd (splitTorus _ D.X).hom (thickObj R ⊥ 0 H).hom))
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) H'.flip ⟨⟨‹_›, ‹_›⟩, (inferInstance : QuasiCompact c.q.left)⟩ a1

theorem Ray.smooth_q {oa : D.OAct O} (Y : Ray oa) : Smooth Y.q.left := by
  obtain ⟨c⟩ := GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0
  have hc := smooth_gtCoord_q c
  let F := fstG (⊥ : Ideal R) 0 Y.H
  let j := inv F.left
  have hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0 := Over.w F

  let ξ := Y.Φ Y.H (𝟙 _)
  obtain ⟨x, hx⟩ := GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ

  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by
    rw [← hF]; exact IsIso.inv_hom_id_assoc _ _)
  let b : Y.H ⟶ Y.H := (Y.Φ Y.H).symm ξ'
  have hb : Y.Φ Y.H b = ξ' := Equiv.apply_symm_apply _ _
  let a := x ≫ F.left
  have ha : a ≫ Y.H.hom = Y.H.hom := by
    rw [Category.assoc, hF]
    exact GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx
  let a' : Y.H ⟶ Y.H := Over.homMk a ha
  have haj : a ≫ j = x := by simp [a, j]

  have e1 : b.left ≫ x = j := by
    have h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _)) := Y.rep.1 Y.H Y.H b (𝟙 _)
    rw [Category.comp_id, hb] at h1
    exact (GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'
  have e1' : b.left ≫ a = 𝟙 _ := by
    rw [← Category.assoc, e1]; simp [j]

  have e2 : a' ≫ b = 𝟙 _ := by
    have h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b)) := Y.rep.1 Y.H Y.H a' b
    rw [hb] at h2
    have h3 := GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2
    rw [haj] at h3
    exact (Y.Φ Y.H).injective (h3.unique_right c hx)
  have e2' : a ≫ b.left = 𝟙 _ := congrArg (·.left) e2
  have : IsIso a := ⟨⟨b.left, e2', e1'⟩⟩
  have hq : Y.q.left = a ≫ j ≫ c.q.left ≫ pullback.fst D.P.A.hom (thick R ⊥ 0) := by
    rw [← Category.assoc a j, haj, ← GlobalTheory.TorusCoord.pG_left]
    exact hx.1
  rw [hq]
  infer_instance

end GlobalTheory.RayEv
end
end

section

open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical


theorem _root_.GlobalTheory.T.conjugateEvaluationMap_smooth_automorphic_values : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, IsAutFunSm R.θ (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u) := by
  exact @GlobalTheory.ConjEvalAut.conjMap_isAutFunSm_see
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem reL_symm_reL_self {E : Type} [Field E] [NumberField E] {a b : ℕ} (h : a = b) (L : Submodule (𝓞 E) (Fin a → E)) :
    reL h.symm (reL h L) = L := by
  subst h
  rw [Formalism.L2.Forms.reL_rfl, Formalism.L2.Forms.reL_rfl]



theorem chart_Uloc_le_levelVL_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ β v, v ∈ Q → ((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom ≤ levelVL (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X (B.R.m - 1)).gram v Lb0 := by
  intro B X I hI hP l Z Ch0 chOf0 F u a Q h1 Ch _ chOf K g _ hStd _ hRd _ _ Lb0 hLb β v _
  obtain ⟨k, H, -⟩ := hRd
  obtain ⟨c0⟩ := GlobalTheory.Mem.Col2.TC.stepBefore_cl_nonempty I hI u
  obtain ⟨k', H'⟩ := (hStd u).mid (B.R.m - 1) h1 (succ_pred_m _)
  have hKb : (K β).lev.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 := by
    rw [← hLb]
    ext x
    rw [← (F u).levJ_Lb h1 (chOf0 u (B.R.m - 1) c0)]
    exact (H.lb β x).trans (H'.lb _ x).symm
  have hle := (GlobalTheory.Port.formsLev_re (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) (I.rec7 l Z).sp.cm.sig
    ((I.rec7 l Z).sp.X (B.R.m - 1)).gram (gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _))
    (fun _ _ => rfl) (K β).lev v).1
  rw [hKb, reL_symm_reL_self] at hle
  exact hle

end GlobalTheory.Mem.Col2.TC

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.chart_local_group_contains_principal_congruence : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ β v, v ∈ Q → ∃ n : ℕ, 0 < n ∧ ∀ x, Formalism.L2.Herm.InPrinc (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) v n Lb0 x → x ∈ ((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom := by
  first | exact @GlobalTheory.Mem.Col2.AdT.LevQ.chart_contains_princ | exact GlobalTheory.Mem.Col2.AdT.LevQ.chart_contains_princ | (intros; apply GlobalTheory.Mem.Col2.AdT.LevQ.chart_contains_princ <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.moveDown_levelPrime_adelic_factorisation : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → ∀ hβ : chOf ((I.fm l u a).dn i v c.1 g) = β, ∃ (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)) (η : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) (κ : (K β).lev.U), (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) ∧ (∀ v', v' ≠ (eV v).1 → bc (prV (E := (I.rec7 l Z).host.E) v') η.1 = 1) ∧ bc (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) γ.1 * ((K β).y ⟨(I.fm l u a).dn i v c.1 g, hβ⟩).1 = ((K β).y c).1 * η.1 * κ.1 ∧ ((((K β).lev.chi κ)⁻¹ : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) : B.LLˣ) : B.LL) := by
  exact @GlobalTheory.Mem.Col2.DnAdel.move_down_adelic
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.supported_unitary_adelic_integral_with_inverse : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) {n : ℕ} (u : GL (Fin n) (AfE F E)), u ∈ Formalism.L2.Herm.UstdAf hc n → ∀ (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)), Formalism.L2.Col.IsOver v P → (∀ v', v' ≠ v → bc (prV (E := E) v') u = 1) → ∀ g ∈ Formalism.L2.Col.GLint E n P, (∀ r s, adAt F P ((u : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' g.toLinearMap r s)) → ∀ i j, (u : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E ∧ ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E := by
  first | exact @GlobalTheory.Mem.Col2.AdT.IntSplit.int_of_supported | exact GlobalTheory.Mem.Col2.AdT.IntSplit.int_of_supported | (intros; apply GlobalTheory.Mem.Col2.AdT.IntSplit.int_of_supported <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.exists_tame_generators_green_cuspidal_labelling : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D), (∀ j g, ∃ z : ℤ, eExp D j g = z) → GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W → ∃ (L : Lay0 D) (hZ : L.ZOk) (hη : L.EtaOk), IsEmpty L.nd.Loc ∧ GlobalTheory.Mem.Top.TypesTrue L.ntypes cf.P cf.W ∧ L.nd.PlG = D.nd.PlG ∧ HEq L.naut.plGw D.naut.plGw ∧ HEq L.ntypes.cenAmb D.ntypes.cenAmb ∧ HEq L.ntypes.cenMt D.ntypes.cenMt ∧ (∃ Gs : GrpSide (setK D L hZ hη), ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; Gs.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen) ∧ ChiTOk (setK D L hZ hη) (cfK L hZ hη cf) ∧ L.loc = D.loc ∧ HEq (@NData.Om _ _ _ L.nd) (@NData.Om _ _ _ D.nd) ∧ HEq (@NData.instOm _ _ _ L.nd) (@NData.instOm _ _ _ D.nd) ∧ HEq (@NData.algOm _ _ _ L.nd) (@NData.algOm _ _ _ D.nd) ∧ HEq (@NData.plOm _ _ _ L.nd) (@NData.plOm _ _ _ D.nd) := by
  first | exact @GlobalTheory.HeightCounting.TameGrp.exists_tame_generators_cuspidal_labelling | exact GlobalTheory.HeightCounting.TameGrp.exists_tame_generators_cuspidal_labelling | (intros; apply GlobalTheory.HeightCounting.TameGrp.exists_tame_generators_cuspidal_labelling <;> assumption)
end

section

alias GlobalTheory.T.thetaAutomorphicWeilData_preserved_divisionLatticeChange :=
  GlobalTheory.Mem.Top.Bl.ThTTr.thT_setDiv
end
