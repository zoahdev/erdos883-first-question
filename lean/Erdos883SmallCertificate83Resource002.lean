import Erdos883SmallCertificate83Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten83_2 :
    (List.ofFn coreChunks83_2).flatten =
      (coreData83.take (coreResources83 2).q).drop 12 := by
  decide +kernel

theorem coreCheck83_2 :
    ∀ c : Fin 1, (coreChunks83_2 c).all
      (coreResourceRowCheck 76 coreData83 (coreResources83 2)) = true := by
  decide +kernel
#print axioms coreFlatten83_2
#print axioms coreCheck83_2
end Erdos883Verified
