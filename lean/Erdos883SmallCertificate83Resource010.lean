import Erdos883SmallCertificate83Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten83_10 :
    (List.ofFn coreChunks83_10).flatten =
      (coreData83.take (coreResources83 10).q).drop 25 := by
  decide +kernel

theorem coreCheck83_10 :
    ∀ c : Fin 1, (coreChunks83_10 c).all
      (coreResourceRowCheck 76 coreData83 (coreResources83 10)) = true := by
  decide +kernel
#print axioms coreFlatten83_10
#print axioms coreCheck83_10
end Erdos883Verified
