import Erdos883SmallCertificate93Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten93_11 :
    (List.ofFn coreChunks93_11).flatten =
      (coreData93.take (coreResources93 11).q).drop 27 := by
  decide +kernel

theorem coreCheck93_11 :
    ∀ c : Fin 1, (coreChunks93_11 c).all
      (coreResourceRowCheck 93 coreData93 (coreResources93 11)) = true := by
  decide +kernel
#print axioms coreFlatten93_11
#print axioms coreCheck93_11
end Erdos883Verified
