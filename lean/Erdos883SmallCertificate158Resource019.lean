import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_19 :
    (List.ofFn coreChunks158_19).flatten =
      (coreData158.take (coreResources158 19).q).drop 38 := by
  decide +kernel

theorem coreCheck158_19 :
    ∀ c : Fin 1, (coreChunks158_19 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 19)) = true := by
  decide +kernel
#print axioms coreFlatten158_19
#print axioms coreCheck158_19
end Erdos883Verified
