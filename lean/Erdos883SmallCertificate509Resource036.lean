import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_36 :
    (List.ofFn coreChunks509_36).flatten =
      (coreData509.take (coreResources509 36).q).drop 77 := by
  decide +kernel

theorem coreCheck509_36 :
    ∀ c : Fin 1, (coreChunks509_36 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 36)) = true := by
  decide +kernel
#print axioms coreFlatten509_36
#print axioms coreCheck509_36
end Erdos883Verified
