import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_37 :
    (List.ofFn coreChunks509_37).flatten =
      (coreData509.take (coreResources509 37).q).drop 78 := by
  decide +kernel

theorem coreCheck509_37 :
    ∀ c : Fin 1, (coreChunks509_37 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 37)) = true := by
  decide +kernel
#print axioms coreFlatten509_37
#print axioms coreCheck509_37
end Erdos883Verified
