import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_57 :
    (List.ofFn coreChunks509_57).flatten =
      (coreData509.take (coreResources509 57).q).drop 107 := by
  decide +kernel

theorem coreCheck509_57 :
    ∀ c : Fin 1, (coreChunks509_57 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 57)) = true := by
  decide +kernel
#print axioms coreFlatten509_57
#print axioms coreCheck509_57
end Erdos883Verified
