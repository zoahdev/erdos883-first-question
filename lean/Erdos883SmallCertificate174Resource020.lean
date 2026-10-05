import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_20 :
    (List.ofFn coreChunks174_20).flatten =
      (coreData174.take (coreResources174 20).q).drop 45 := by
  decide +kernel

theorem coreCheck174_20 :
    ∀ c : Fin 1, (coreChunks174_20 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 20)) = true := by
  decide +kernel
#print axioms coreFlatten174_20
#print axioms coreCheck174_20
end Erdos883Verified
