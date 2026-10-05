import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_7 :
    (List.ofFn coreChunks680_7).flatten =
      (coreData680.take (coreResources680 7).q).drop 91 := by
  decide +kernel

theorem coreCheck680_7 :
    ∀ c : Fin 2, (coreChunks680_7 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 7)) = true := by
  decide +kernel
#print axioms coreFlatten680_7
#print axioms coreCheck680_7
end Erdos883Verified
