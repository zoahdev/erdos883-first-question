import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_16 :
    (List.ofFn coreChunks158_16).flatten =
      (coreData158.take (coreResources158 16).q).drop 33 := by
  decide +kernel

theorem coreCheck158_16 :
    ∀ c : Fin 1, (coreChunks158_16 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 16)) = true := by
  decide +kernel
#print axioms coreFlatten158_16
#print axioms coreCheck158_16
end Erdos883Verified
