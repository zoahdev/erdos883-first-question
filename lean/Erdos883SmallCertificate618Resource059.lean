import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_59 :
    (List.ofFn coreChunks618_59).flatten =
      (coreData618.take (coreResources618 59).q).drop 121 := by
  decide +kernel

theorem coreCheck618_59 :
    ∀ c : Fin 1, (coreChunks618_59 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 59)) = true := by
  decide +kernel
#print axioms coreFlatten618_59
#print axioms coreCheck618_59
end Erdos883Verified
