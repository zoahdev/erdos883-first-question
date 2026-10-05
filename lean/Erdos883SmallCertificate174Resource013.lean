import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_13 :
    (List.ofFn coreChunks174_13).flatten =
      (coreData174.take (coreResources174 13).q).drop 34 := by
  decide +kernel

theorem coreCheck174_13 :
    ∀ c : Fin 1, (coreChunks174_13 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 13)) = true := by
  decide +kernel
#print axioms coreFlatten174_13
#print axioms coreCheck174_13
end Erdos883Verified
