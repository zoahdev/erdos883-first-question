import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_41 :
    (List.ofFn coreChunks509_41).flatten =
      (coreData509.take (coreResources509 41).q).drop 85 := by
  decide +kernel

theorem coreCheck509_41 :
    ∀ c : Fin 1, (coreChunks509_41 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 41)) = true := by
  decide +kernel
#print axioms coreFlatten509_41
#print axioms coreCheck509_41
end Erdos883Verified
