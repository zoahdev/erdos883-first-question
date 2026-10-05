import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_6 :
    (List.ofFn coreChunks509_6).flatten =
      (coreData509.take (coreResources509 6).q).drop 69 := by
  decide +kernel

theorem coreCheck509_6 :
    ∀ c : Fin 1, (coreChunks509_6 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 6)) = true := by
  decide +kernel
#print axioms coreFlatten509_6
#print axioms coreCheck509_6
end Erdos883Verified
