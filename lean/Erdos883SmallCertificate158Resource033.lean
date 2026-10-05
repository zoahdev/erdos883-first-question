import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_33 :
    (List.ofFn coreChunks158_33).flatten =
      (coreData158.take (coreResources158 33).q).drop 52 := by
  decide +kernel

theorem coreCheck158_33 :
    ∀ c : Fin 1, (coreChunks158_33 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 33)) = true := by
  decide +kernel
#print axioms coreFlatten158_33
#print axioms coreCheck158_33
end Erdos883Verified
