import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_41 :
    (List.ofFn coreChunks618_41).flatten =
      (coreData618.take (coreResources618 41).q).drop 91 := by
  decide +kernel

theorem coreCheck618_41 :
    ∀ c : Fin 1, (coreChunks618_41 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 41)) = true := by
  decide +kernel
#print axioms coreFlatten618_41
#print axioms coreCheck618_41
end Erdos883Verified
