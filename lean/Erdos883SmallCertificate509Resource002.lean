import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_2 :
    (List.ofFn coreChunks509_2).flatten =
      (coreData509.take (coreResources509 2).q).drop 49 := by
  decide +kernel

theorem coreCheck509_2 :
    ∀ c : Fin 1, (coreChunks509_2 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 2)) = true := by
  decide +kernel
#print axioms coreFlatten509_2
#print axioms coreCheck509_2
end Erdos883Verified
