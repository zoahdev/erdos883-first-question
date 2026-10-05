import Erdos883SmallCertificate83Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten83_15 :
    (List.ofFn coreChunks83_15).flatten =
      (coreData83.take (coreResources83 15).q).drop 0 := by
  decide +kernel

theorem coreCheck83_15 :
    ∀ c : Fin 2, (coreChunks83_15 c).all
      (coreResourceRowCheck 76 coreData83 (coreResources83 15)) = true := by
  decide +kernel
#print axioms coreFlatten83_15
#print axioms coreCheck83_15
end Erdos883Verified
