import Erdos883SmallCertificate93Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten93_7 :
    (List.ofFn coreChunks93_7).flatten =
      (coreData93.take (coreResources93 7).q).drop 21 := by
  decide +kernel

theorem coreCheck93_7 :
    ∀ c : Fin 1, (coreChunks93_7 c).all
      (coreResourceRowCheck 93 coreData93 (coreResources93 7)) = true := by
  decide +kernel
#print axioms coreFlatten93_7
#print axioms coreCheck93_7
end Erdos883Verified
