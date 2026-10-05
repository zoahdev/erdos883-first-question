import Erdos883SmallCertificate83Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten83_3 :
    (List.ofFn coreChunks83_3).flatten =
      (coreData83.take (coreResources83 3).q).drop 13 := by
  decide +kernel

theorem coreCheck83_3 :
    ∀ c : Fin 1, (coreChunks83_3 c).all
      (coreResourceRowCheck 76 coreData83 (coreResources83 3)) = true := by
  decide +kernel
#print axioms coreFlatten83_3
#print axioms coreCheck83_3
end Erdos883Verified
