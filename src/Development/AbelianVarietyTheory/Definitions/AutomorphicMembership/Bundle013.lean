module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle011
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle012
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FrobOrderSpec
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.GTiedFOfIsRecCEv
import Formalism.LocalToGlobal.GroupLattices.TiedRec
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

def assemble (B : Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) : D7 where
  R := B.R
  host := B.host
  sp := B.sp
  vol := G.vol
  vol_pos := G.vol_pos
  what₂ := W.what₂
  eTau := Equiv.refl _
  hc := B.hc
  wordFin := B.wordFin
  u₀ := B.u₀
  hcW := B.hcW
  hcW_base := B.hcW_base
  hcW_v := B.hcW_v
  hcW_b := B.hcW_b
  hcW_e := B.hcW_e
  hcW_first := B.hcW_first
  hcW_last := B.hcW_last
  mem := C.mem
  nfLL := B.nfLL
  starLL := B.starLL
  tcLL := B.tcLL
  galLL := B.galLL
  starLL_cx := B.starLL_cx
  div := V.div
  div_good := V.div_good
  embE := B.embE
  embE_φ₀ := B.embE_φ₀
  conjF := B.toPre.conjF
  conjF_eq := B.toPre.conjF_eq
  embE_conj := B.embE_conj
  LL0 := B.LL0
  hostField_le_fixedField := B.hostField_le_fixedField
  O_int := B.O_int
  O_contains := B.O_contains
  plEq := Equiv.refl _
  val_eq := Formalism.BasicNotions.Examples₂.placesOf_val_eq B.LL
  ram_eq := Formalism.BasicNotions.Examples₂.placesOf_ram_eq B.LL
  conj_val := Formalism.BasicNotions.Examples₂.placesOf_conj_val B.LL
  T_level := fun u => by rw [C.A_T]; exact B.T_level u
  T_norm := fun u => by rw [C.A_T]; exact B.T_norm u
  sp_T := by rw [C.A_T]; exact B.sp_T
  cOf := B.cOf
  cOf_ne := B.cOf_ne
  cOf_eq := fun u => by rw [C.A_T, C.A_T]; exact B.cOf_eq u
  T_win := fun u => by
    simp only [ColumnsAtT.Tstar, ColumnsAtT.Xu, C.A_T, C.A_duStar, C.A_Dstar, C.A_GamP]
    exact B.T_win u
  GamP_eq := fun u => (C.A_GamP u).trans (C.A_GamP B.u₀).symm
  T_ne_pde := fun u => by rw [C.A_T]; exact B.T_ne_pde u
  Dstar_eq := C.A_Dstar
  clsLat := C.clsLat
  clsLat_lat u i c :=
    show Submodule.IsFullLattice B.host.E (C.clsLat u i c) from C.clsLat_lat u i c
  eMu := W.eMu
  eMt := W.eMt0
  perCol_base_eq_PtilCol := W.perCol_base_eq_PtilCol
  Bu_linL := W.Bu_linL
  Bu_linR := W.Bu_linR
  chTw := C.chTw
  memberColumns_twistedChain_base := C.memberColumns_twistedChain_base
  e0Tw := C.e0Tw
  PTw := C.PTw
  eMtTw := W.eMtTw
  perCol_tie := W.perCol_tie
  jEE := V.jEE
  jEE_basis := V.jEE_basis
  jN := V.jN
  jN_basis := V.jN_basis
  Dall_eq := V.Dall_eq
  delP_eq := V.delP_eq
  Dt := C.Dt
  instDt := C.instDt
  detCls := C.detCls
  muTil := C.muTil
  chiD := C.chiD
  UO := C.UO
  chiD_UO := C.chiD_UO
  e1Dt := C.e1Dt
  rest_detCharacter_on_unitary_eq := C.rest_detCharacter_on_unitary_eq
  relDet := C.relDet
  relDet_self := C.relDet_self
  relDet_mul := C.relDet_mul
  relDet_smul := C.relDet_smul
  rhoDet_eq_inv_muTilde_chiD_pow := C.rhoDet_eq_inv_muTilde_chiD_pow
  rhoDetPrime_eq_muTilde_mul_chi_pow := C.rhoDetPrime_eq_muTilde_mul_chi_pow
  dsig := S.dsig
  dsig_pos := S.dsig_pos
  s := S.s
  s_split := S.s_split
  s_HH := S.s_HH
  s_Cu := S.s_Cu
  s_PlF := S.s_PlF
  loc := N.loc
  locA := N.locA
  locT := N.locT
  nd := N.nd
  ntw := N.ntw
  naut := N.naut
  nbc := N.nbc
  nexp := N.nexp
  ntypes := N.ntypes
  nStage_trivialCharacter_compat := N.nStage_trivialCharacter_compat
  nStage_trivialCharacter_coeff_eq := N.nStage_trivialCharacter_coeff_eq
  nth := N.nth
  nbr := N.nbr
  nbr_ind := N.nbr_ind
  self_good := N.self_good
  ntwbr := N.ntwbr
  ntwbr_ind := N.ntwbr_ind
  loc_tie := N.loc_tie
  bc_tie := N.bc_tie
  rbar_tie := N.rbar_tie
  mtpar_tie := N.mtpar_tie
  Z_tie := N.Z_tie
  Zgood_tie := N.Zgood_tie
  etaJ_tie := N.etaJ_tie
  fm := C.fm
  eMu_isom := W.eMu_isom
  nuIn := V.nuIn
  nuIn_inj := V.nuIn_inj
  nuIn_range := V.nuIn_range
  nuIn_jN := V.nuIn_jN
  nuIn_norm := V.nuIn_norm
  jEE_norm := V.jEE_norm
  s_Cu_isom := S.s_Cu_isom
  sEE := S.sEE
  cd := G.cd
  jet := G.jet
  jetU := G.jetU
  jetL := G.jetL
  jetL' := G.jetL'
  jetW := G.jetW
  jetW_l := G.jetW_l
  jetTau := G.jetTau
  jetW1 := G.jetW1
  resChar_thetaJetPlaceDegOne := G.resChar_thetaJetPlaceDegOne
  jetTau1 := G.jetTau1
  jetU1 := G.jetU1
  jetL1 := G.jetL1
  jetL1' := G.jetL1'
  gx := G.gx
  gat := G.gat
  gat_d := G.gat_d
  Y_sigval := B.Y_sigval

section
variable (B : Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C)

end

structure Stages where
  B : Base
  C : Cols B
  W : RowsRest B C
  V : DivStage B C W
  S : SStage B C W
  N : NStage B C W
  G : GJStage B C

def Stages.toD7 (X : Stages) : D7 := assemble X.B X.C X.W X.V X.S X.N X.G

end GlobalTheory.Mem

end
end

section

noncomputable section

open Formalism.BasicNotions NumberField Formalism.L2.DIV Formalism.IndefR.Cx

namespace GlobalTheory.Mem.R3.MjModel

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem unitMap_norm (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (x : (unitLat K (Module.finrank ℂ W)).V) :
    Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (unitLat K (Module.finrank ℂ W)).b (unitLat K (Module.finrank ℂ W)).X
      (InfinitePlace.mk σ) x) = ‖unitMap σ W x‖ := by
  have h1 : unitMap σ W x = ∑ i, σ (x i) • stdOrthonormalBasis ℂ W i :=
    Fintype.linearCombination_apply ℂ (stdOrthonormalBasis ℂ W) (cpt σ x)
  have h2 : ‖unitMap σ W x‖ ^ 2 = ∑ i, ‖σ (x i)‖ ^ 2 := by
    rw [← (stdOrthonormalBasis ℂ W).sum_sq_norm_inner_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1, (stdOrthonormalBasis ℂ W).orthonormal.inner_right_fintype]
  rw [← Real.sqrt_sq (norm_nonneg (unitMap σ W x)), h2, Formalism.HermitianLatticesTheory.cnorm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h3 : Formalism.HermitianLatticesTheory.fcoord (unitLat K (Module.finrank ℂ W)).b (unitLat K (Module.finrank ℂ W)).X (InfinitePlace.mk σ) x i =
      (InfinitePlace.mk σ).embedding (x i) := by
    have h4 : ∀ (n : ℕ) (u : Fin n → ℂ), Matrix.mulVec (1 : Matrix (Fin n) (Fin n) ℂ)⁻¹ u = u := fun n u => by
      rw [inv_one, Matrix.one_mulVec]
    exact congrFun (h4 _ _) i
  rw [h3, InfinitePlace.norm_embedding_eq, InfinitePlace.apply]

section Record

open Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0} (Z : ReadL R F X0 Y)

theorem jM_metric_all (hH : Holds R F) (j : ℕ) (x : (mjH Z j).V) :
    Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (mjH Z j).b (mjH Z j).X (InfinitePlace.mk D.what₂.embLL) x) = ‖jM Z j x‖ :=
  mapSeq_ind_all _ _ D.what₂.Mj Z.jW
    (fun _ A g => ∀ x : A.V, Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord A.b A.X (InfinitePlace.mk D.what₂.embLL) x) = ‖g x‖)
    (fun i => MjCoord.jW_norm Z hH i) (fun _ => unitMap_norm _ _) j x

end Record

end GlobalTheory.Mem.R3.MjModel

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms

namespace GlobalTheory.Mem.LocalPack

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

section Ext

variable {Os Ks O Kf O' Kf' : Type} [CommRing Os] [Field Ks] [Algebra Os Ks] [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Field Kf']
  [Algebra O' Kf']

end Ext

section Ties

abbrev RingTie := @Formalism.L2.G.RingCompatibleAt

abbrev LocalIs := @Formalism.L2.G.GatIs

alias standardSub_of_ringTie := Formalism.L2.G.stdSubAt_of_ring

alias localIs_of_hyperspecial := Formalism.L2.G.gatIs_recG

alias ringTie_record := Formalism.L2.G.ringTied_recC

end Ties

section Bridge

theorem pack_eq (D : D7) (u : D.what₂.Word)
    (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)) (w : D.what₂.places.Pl)
    (h5 : 5 ≤ D.what₂.places.resChar w) (h2 : 2 ≤ nFr D (D.what₂.places.resChar w))
    (he : Even (nFr D (D.what₂.places.resChar w)))
    (I : LocId Lc (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : Formalism.L2.Herm.awayFrom₂ Lc (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ) :
    pack D u Lc w h5 h2 he I ψ = locPackC D u Lc w h5 h2 he I ψ := by
  first
    | with_reducible rfl
    | (delta pack locPackC frobOrder nFr; with_reducible rfl)

end Bridge

section Record

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)

end Record

abbrev IsConcrete := @Formalism.L2.G.IsRecC

end GlobalTheory.Mem.LocalPack
end
end
