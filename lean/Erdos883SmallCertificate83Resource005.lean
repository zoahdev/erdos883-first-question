import Erdos883SmallCertificate83Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten83_5 :
    (List.ofFn coreChunks83_5).flatten =
      (coreData83.take (coreResources83 5).q).drop 17 := by
  decide +kernel

theorem coreCheck83_5 :
    ∀ c : Fin 1, (coreChunks83_5 c).all
      (coreResourceRowCheck 76 coreData83 (coreResources83 5)) = true := by
  decide +kernel
#print axioms coreFlatten83_5
#print axioms coreCheck83_5
end Erdos883Verified
