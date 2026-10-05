import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_14 :
    (List.ofFn coreChunks158_14).flatten =
      (coreData158.take (coreResources158 14).q).drop 31 := by
  decide +kernel

theorem coreCheck158_14 :
    ∀ c : Fin 1, (coreChunks158_14 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 14)) = true := by
  decide +kernel
#print axioms coreFlatten158_14
#print axioms coreCheck158_14
end Erdos883Verified
