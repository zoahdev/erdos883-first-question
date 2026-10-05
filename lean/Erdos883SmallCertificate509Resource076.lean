import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_76 :
    (List.ofFn coreChunks509_76).flatten =
      (coreData509.take (coreResources509 76).q).drop 148 := by
  decide +kernel

theorem coreCheck509_76 :
    ∀ c : Fin 1, (coreChunks509_76 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 76)) = true := by
  decide +kernel
#print axioms coreFlatten509_76
#print axioms coreCheck509_76
end Erdos883Verified
