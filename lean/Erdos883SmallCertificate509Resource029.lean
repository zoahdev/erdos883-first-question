import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_29 :
    (List.ofFn coreChunks509_29).flatten =
      (coreData509.take (coreResources509 29).q).drop 124 := by
  decide +kernel

theorem coreCheck509_29 :
    ∀ c : Fin 1, (coreChunks509_29 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 29)) = true := by
  decide +kernel
#print axioms coreFlatten509_29
#print axioms coreCheck509_29
end Erdos883Verified
