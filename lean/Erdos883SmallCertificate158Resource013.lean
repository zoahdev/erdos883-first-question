import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_13 :
    (List.ofFn coreChunks158_13).flatten =
      (coreData158.take (coreResources158 13).q).drop 30 := by
  decide +kernel

theorem coreCheck158_13 :
    ∀ c : Fin 1, (coreChunks158_13 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 13)) = true := by
  decide +kernel
#print axioms coreFlatten158_13
#print axioms coreCheck158_13
end Erdos883Verified
