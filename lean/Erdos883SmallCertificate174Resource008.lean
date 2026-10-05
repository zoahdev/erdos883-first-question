import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_8 :
    (List.ofFn coreChunks174_8).flatten =
      (coreData174.take (coreResources174 8).q).drop 20 := by
  decide +kernel

theorem coreCheck174_8 :
    ∀ c : Fin 1, (coreChunks174_8 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 8)) = true := by
  decide +kernel
#print axioms coreFlatten174_8
#print axioms coreCheck174_8
end Erdos883Verified
