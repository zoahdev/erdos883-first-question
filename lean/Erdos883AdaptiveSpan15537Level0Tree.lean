import Erdos883AdaptiveSpan15537Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength15537_0 : adaptiveNumericSpans15537_0.length = 402 := by decide +kernel
theorem adaptiveSpanEvenCache15537_0 : adaptiveSpanEven15537_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain15537_0 : adaptiveSpanEven15537_0.domainCheck 7769 = true := by decide +kernel
theorem adaptiveSpanEvenEntries15537_0 : adaptiveSpanEven15537_0.spans = coreEvenSpans 7769 0 adaptiveNumericSpans15537_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache15537_0 : adaptiveSpanWhole15537_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain15537_0 : adaptiveSpanWhole15537_0.domainCheck 7769 = true := by decide +kernel
theorem adaptiveSpanWholeEntries15537_0 : adaptiveSpanWhole15537_0.spans = coreWholeSpans 0 adaptiveNumericSpans15537_0 := by
  decide +kernel
end Erdos883Verified
