import Erdos883SmallCertificate83Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten83_9 :
    (List.ofFn coreChunks83_9).flatten =
      (coreData83.take (coreResources83 9).q).drop 24 := by
  decide +kernel

theorem coreCheck83_9 :
    ∀ c : Fin 1, (coreChunks83_9 c).all
      (coreResourceRowCheck 76 coreData83 (coreResources83 9)) = true := by
  decide +kernel
#print axioms coreFlatten83_9
#print axioms coreCheck83_9
end Erdos883Verified
