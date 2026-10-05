import Erdos883AdaptiveSpan20682Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength20682_0 : adaptiveNumericSpans20682_0.length = 430 := by decide +kernel
theorem adaptiveSpanEvenCache20682_0 : adaptiveSpanEven20682_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain20682_0 : adaptiveSpanEven20682_0.domainCheck 10341 = true := by decide +kernel
theorem adaptiveSpanEvenEntries20682_0 : adaptiveSpanEven20682_0.spans = coreEvenSpans 10341 0 adaptiveNumericSpans20682_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache20682_0 : adaptiveSpanWhole20682_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain20682_0 : adaptiveSpanWhole20682_0.domainCheck 10341 = true := by decide +kernel
theorem adaptiveSpanWholeEntries20682_0 : adaptiveSpanWhole20682_0.spans = coreWholeSpans 0 adaptiveNumericSpans20682_0 := by
  decide +kernel
end Erdos883Verified
