import Erdos883AdaptiveSpan25027Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength25027_0 : adaptiveNumericSpans25027_0.length = 450 := by decide +kernel
theorem adaptiveSpanEvenCache25027_0 : adaptiveSpanEven25027_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain25027_0 : adaptiveSpanEven25027_0.domainCheck 12514 = true := by decide +kernel
theorem adaptiveSpanEvenEntries25027_0 : adaptiveSpanEven25027_0.spans = coreEvenSpans 12514 0 adaptiveNumericSpans25027_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache25027_0 : adaptiveSpanWhole25027_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain25027_0 : adaptiveSpanWhole25027_0.domainCheck 12514 = true := by decide +kernel
theorem adaptiveSpanWholeEntries25027_0 : adaptiveSpanWhole25027_0.spans = coreWholeSpans 0 adaptiveNumericSpans25027_0 := by
  decide +kernel
end Erdos883Verified
