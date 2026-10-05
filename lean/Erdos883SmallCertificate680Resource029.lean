import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_29 :
    (List.ofFn coreChunks680_29).flatten =
      (coreData680.take (coreResources680 29).q).drop 147 := by
  decide +kernel

theorem coreCheck680_29 :
    ∀ c : Fin 1, (coreChunks680_29 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 29)) = true := by
  decide +kernel
#print axioms coreFlatten680_29
#print axioms coreCheck680_29
end Erdos883Verified
